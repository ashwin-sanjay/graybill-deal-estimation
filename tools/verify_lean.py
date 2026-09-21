#!/usr/bin/env python3
"""Verify current source modules, exact kernel replay, and all owned axioms.

Run this program in the pinned Lean 4.31.0 dependency environment. --static performs
source checks without invoking Lean, Lake, Elan, or a compiler.
"""
from __future__ import annotations
import argparse, concurrent.futures, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time

ROOT=pathlib.Path(__file__).resolve().parents[1]
ALLOWED={'propext','Classical.choice','Quot.sound'}
TOOLCHAIN='leanprover/lean4:v4.31.0'


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def digest(value): return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def read(path): return json.loads(path.read_text(encoding='utf-8'))
def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def emit(value): print(json.dumps(value,ensure_ascii=False,separators=(',',':')),flush=True)
def inside(value):
    path=pathlib.Path(value)
    if path.is_absolute() or '..' in path.parts:raise ValueError('Expected a relative input path')
    path=(ROOT/path).resolve()
    if not path.is_relative_to(ROOT):raise ValueError('Input escapes source root')
    return path


def imports(path):
    # Published mathematical sources contain no presentation comments.
    text=path.read_text(encoding='utf-8')
    result=[]
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',text,re.M):
        result.extend(n for n in line.split() if n!='all')
    return list(dict.fromkeys(result))


def static_check(manifest):
    if manifest.get('schemaVersion')!=1 or manifest.get('toolchain')!=TOOLCHAIN:raise ValueError('Unsupported manifest/toolchain')
    rows=manifest['modules'];byname={r['module']:r for r in rows}
    if not rows:raise ValueError('Empty project manifest')
    if len(byname)!=len(rows) or len({r['path'].casefold() for r in rows})!=len(rows):raise ValueError('Duplicate module/path')
    for r in rows:
        if not re.fullmatch(r'GD\.Module\d+',r['module']):raise ValueError('Unexpected project module name')
        if r['path']!=r['module'].replace('.','/')+'.lean':raise ValueError('Module/source mismatch')
        for field in ['expectedDeclarations','expectedPrivateDeclarations']:
            expected=r.get(field,[])
            if not isinstance(expected,list) or any(not isinstance(n,str) or not n for n in expected):raise ValueError('Invalid expected declaration list')
            if len(set(expected))!=len(expected):raise ValueError('Duplicate expected declaration')
        p=inside(r['path'])
        if sha(p)!=r['sha256']:raise ValueError('Changed current source: '+r['path'])
        if imports(p)!=r['imports']:raise ValueError('Changed source imports: '+r['path'])
        for name in r['imports']:
            if name.startswith('GD.') and name not in byname:raise ValueError('Missing project dependency '+name)
    visited=set();active=set()
    def visit(name):
        if name in visited:return
        if name in active:raise ValueError('Module import cycle')
        active.add(name)
        for dep in byname[name]['imports']:
            if dep in byname:visit(dep)
        active.remove(name);visited.add(name)
    for name in byname:visit(name)
    checks=manifest.get('statementChecks')
    if not checks:raise ValueError('Missing public statement verification gates')
    if checks:
        ref=byname[checks['referenceModule']];byname[checks['bridgeModule']]
        source=inside(ref['path']).read_text(encoding='utf-8')
        for mutation in checks['negativeMutations']:
            if source.count(mutation['old'])!=1 or mutation['old']==mutation['new']:raise ValueError('Invalid statement mutation '+mutation['name'])
        if len(checks['claims'])!=3 or len(checks['nonvacuity'])!=4 or len(checks['negativeMutations'])!=2:raise ValueError('Incomplete statement gates')
    return byname


def match_private_declarations(rows,module,expected_private=()):
    if len(set(expected_private))!=len(expected_private):raise ValueError('Duplicate expected private declaration')
    matches={}
    for canonical in expected_private:
        if not isinstance(canonical,str) or not canonical or canonical.startswith('_private.'):
            raise ValueError('Expected a canonical private declaration name')
        pattern=re.compile(r'_private\.'+re.escape(module)+r'\.[0-9]+\.'+re.escape(canonical))
        found=[row['name'] for row in rows if row.get('owner_module')==module and pattern.fullmatch(row['name'])]
        if len(found)!=1:
            raise ValueError('Missing or ambiguous expected private declaration: '+canonical)
        matches[canonical]=found[0]
    if len(set(matches.values()))!=len(matches):raise ValueError('Private declarations do not match uniquely')
    return matches


def validate_audit(value,module,expected=(),expected_private=()):
    if value.get('schema_version')!=1 or value.get('target_module')!=module or value.get('lean_version')!='4.31.0':raise ValueError('Audit identity mismatch')
    audit=value['audit'];rows=audit['declarations'];names={r['name'] for r in rows}
    if audit['declaration_count']!=len(rows) or len(names)!=len(rows):raise ValueError('Owned declaration enumeration mismatch')
    if not set(expected)<=names:raise ValueError('Expected explicit declarations missing: '+str(sorted(set(expected)-names)))
    match_private_declarations(rows,module,expected_private)
    if audit.get('uses_sorryAx') or audit.get('nonstandard_axioms') or audit.get('declarations_using_nonstandard_axioms') or audit.get('owned_axiom_count'):raise ValueError('Disallowed owned/imported axioms')
    if not set(audit['all_axioms'])<=ALLOWED:raise ValueError('Disallowed aggregate axioms')
    if audit['theorem_count']!=sum(r['kind']=='theorem' for r in rows):raise ValueError('Theorem count mismatch')
    for row in rows:
        if row['owner_module']!=module or row.get('uses_sorryAx') or row.get('nonstandard_axioms') or not set(row['axioms'])<=ALLOWED:raise ValueError('Disallowed declaration axioms')
    return audit


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest',default='verification/modules.json');ap.add_argument('--static',action='store_true')
    ap.add_argument('--jobs',type=int,default=4);ap.add_argument('--lean-threads',type=int,default=2)
    ap.add_argument('--timeout',type=int,default=1800,help='Maximum seconds per compiler/kernel/audit stage')
    ap.add_argument('--output',type=pathlib.Path);ap.add_argument('--module',action='append',dest='targets')
    ap.add_argument('--emit-audits',action='store_true')
    args=ap.parse_args();manifest_path=inside(args.manifest);manifest=read(manifest_path);byname=static_check(manifest)
    if args.static:emit({'status':'passed','scope':'Current hashes, literal imports, acyclic project closure, statement control inputs; no Lean execution','modules':len(byname)});return 0
    if not 1<=args.jobs<=64 or not 1<=args.lean_threads<=16 or not 60<=args.timeout<=43200:raise ValueError('Invalid resource bound')
    output=args.output.resolve() if args.output else ROOT/'.build'/('verification-'+str(time.time_ns()))
    output.mkdir(parents=True,exist_ok=False);lib=output/'lib';lib.mkdir();logs=output/'logs';logs.mkdir()
    # Lake resolves the pinned installed compiler and public dependency environment.
    def lake(*argv):return subprocess.check_output(['lake','env',*argv],cwd=ROOT,text=True,timeout=args.timeout).strip()
    version=lake('lean','--version')
    if not version.startswith('Lean (version 4.31.0,'):raise ValueError('Wrong compiler version '+version)
    prefix=pathlib.Path(lake('lean','--print-prefix'));lean=prefix/'bin/lean'
    base_env=dict(os.environ);base_env['LEAN_SYSROOT']=str(prefix);base_env['ELAN_TOOLCHAIN']=TOOLCHAIN
    package_path=lake('printenv','LEAN_PATH')
    def environment(paths):
        env=dict(base_env);env['LEAN_PATH']=os.pathsep.join([*(str(p) for p in paths),package_path]);return env
    compiler={'toolchain':TOOLCHAIN,'version':version,'leanSha256':sha(lean),'leancheckerSha256':sha(prefix/'bin/leanchecker')}
    tools={p:sha(inside(p)) for p in ['tools/verify_lean.py','tools/AuditModule.lean','tools/ReplayModule.lean']}
    packages=read(ROOT/'lake-manifest.json')['packages'];package_records=[]
    for pkg in packages:
        p=ROOT/'.lake/packages'/pkg['name']
        rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()
        if rev!=pkg['rev']:raise ValueError('Dependency revision mismatch '+pkg['name'])
        if subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=p).returncode!=0:raise ValueError('Modified tracked dependency sources '+pkg['name'])
        package_records.append({'name':pkg['name'],'revision':rev,'url':pkg['url']})
    inputs={'manifestSha256':sha(manifest_path),'compiler':compiler,'tools':tools,'lakeManifestSha256':sha(ROOT/'lake-manifest.json'),'packages':package_records,'flags':['-j'+str(args.lean_threads),'-DwarningAsError=true','-Dlinter.all=false']}
    selected=set()
    def select(n):
        if n in selected:return
        if n not in byname:raise ValueError('Unknown selected module '+n)
        selected.add(n)
        for dep in byname[n]['imports']:
            if dep in byname:select(dep)
    for n in args.targets or byname:select(n)
    report={'schemaVersion':1,'status':'running','inputs':inputs,'started':time.time(),'requested':sorted(args.targets or []),'selectedCount':len(selected),'fullModuleCount':len(byname),'moduleResults':[],'statementChecks':None,'scope':'Fresh current project compilation, exact-module kernel replay and all-owned axiom audit; pinned compiler/core and package cache remain the explicit trust boundary.'}
    emit({'event':'verification-start','inputs':inputs,'selectedCount':len(selected),'fullModuleCount':len(byname)})
    def run(command,path,paths):
        started=time.monotonic();code=None;error=None
        with path.open('w',encoding='utf-8') as out:
            try:code=subprocess.run(command,cwd=ROOT,env=environment(paths),stdout=out,stderr=subprocess.STDOUT,timeout=args.timeout).returncode
            except subprocess.TimeoutExpired:error='stage timeout'
        return {'command':command,'exitCode':code,'error':error,'seconds':round(time.monotonic()-started,3),'logSha256':sha(path)}
    audits={};completed={};failed=set();stage_flags=inputs['flags']
    def compile_one(name):
        row=byname[name];start=time.monotonic();base=logs/name.replace('.','_');source=inside(row['path']);obj=lib/pathlib.Path(*name.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        stamp={'source':row['sha256'],'module':name,'imports':row['imports'],'dependencies':{d:completed[d]['fingerprint'] for d in row['imports'] if d in byname},'inputs':inputs}
        result={'module':name,'path':row['path'],'sourceSha256':row['sha256'],'status':'failed','stamp':stamp,'stages':{}}
        try:
            if sha(source)!=row['sha256']:raise ValueError('Source changed during run')
            commands=[('compile',[str(lean),*stage_flags,'--root='+str(ROOT),'-o',str(obj),str(source)]),('kernel',[str(lean),'-j'+str(args.lean_threads),'--run',str(ROOT/'tools/ReplayModule.lean'),name]),('axioms',[str(lean),'-j'+str(args.lean_threads),'--run',str(ROOT/'tools/AuditModule.lean'),name])]
            for stage,command in commands:
                log=pathlib.Path(str(base)+'.'+stage+'.log');record=run(command,log,[lib]);result['stages'][stage]=record
                if record['exitCode']!=0:
                    result['diagnostic']=log.read_text(encoding='utf-8',errors='replace');raise ValueError(stage+' failed')
            kernel=read(pathlib.Path(str(base)+'.kernel.log'));audit_record=read(pathlib.Path(str(base)+'.axioms.log'));audit=validate_audit(audit_record,name,row.get('expectedDeclarations',[]),row.get('expectedPrivateDeclarations',[]))
            if kernel.get('status')!='passed' or kernel.get('target_module')!=name or kernel.get('lean_version')!='4.31.0' or kernel.get('replayed_declaration_count')!=audit['declaration_count']:raise ValueError('Kernel identity/count mismatch')
            if {i['module'] for i in audit_record['direct_imports']}-{'Init'}!=set(row['imports'])-{'Init'}:raise ValueError('Compiled imports differ from manifest')
            if pathlib.Path(kernel['object_path']).resolve()!=obj.resolve() or pathlib.Path(audit_record['object_path']).resolve()!=obj.resolve():raise ValueError('Checker target object mismatch')
            artifacts=[{'path':p.relative_to(output).as_posix(),'sha256':sha(p),'bytes':p.stat().st_size} for p in [obj,pathlib.Path(str(obj)+'.server'),pathlib.Path(str(obj)+'.private'),obj.with_suffix('.ir')] if p.is_file()]
            private_matches=match_private_declarations(audit['declarations'],name,row.get('expectedPrivateDeclarations',[]))
            explicit_count=len(row.get('expectedDeclarations',[]))+len(private_matches)
            result.update(status='passed',declarationCount=audit['declaration_count'],theoremCount=audit['theorem_count'],expectedPublicDeclarationCount=len(row.get('expectedDeclarations',[])),expectedPrivateDeclarationCount=len(private_matches),expectedExplicitDeclarationCount=explicit_count,expectedPrivateDeclarationMatches=private_matches,additionalOwnedDeclarationCount=audit['declaration_count']-explicit_count,allAxioms=audit['all_axioms'],kernel=kernel,artifacts=artifacts)
            if args.emit_audits:result['ownedAudit']=audit_record
            audits[name]=audit_record
        except Exception as exc:result['error']=str(exc)
        result['seconds']=round(time.monotonic()-start,3);result['fingerprint']=digest(result);write(pathlib.Path(str(base)+'.receipt.json'),result);return result
    pending=set(selected);running={}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            for name in sorted(list(pending)):
                deps=set(byname[name]['imports']) & selected
                if deps & failed:
                    result={'module':name,'path':byname[name]['path'],'sourceSha256':byname[name]['sha256'],'status':'blocked-by-failed-dependency','dependencies':sorted(deps&failed)};report['moduleResults'].append(result);emit({'event':'module-result',**result});failed.add(name);pending.remove(name)
                elif len(running)<args.jobs and deps<=completed.keys():running[pool.submit(compile_one,name)]=name;pending.remove(name)
            if not running:
                if pending:continue
                break
            done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                name=running.pop(future);result=future.result();report['moduleResults'].append(result);emit({'event':'module-result',**result})
                if result['status']=='passed':completed[name]=result
                else:failed.add(name)
            write(output/'result.json',report)
    checks=manifest.get('statementChecks')
    if checks and checks['referenceModule'] in selected and checks['bridgeModule'] in selected and not failed:
        try:report['statementChecks']=statement_gates(checks,byname,audits,ROOT,output,lib,lean,stage_flags,run)
        except Exception as error:report['statementChecks']={'status':'failed','error':str(error)}
        emit({'event':'statement-checks','result':report['statementChecks']})
    report['finished']=time.time();report['passedCount']=len(completed);report['failedOrBlockedCount']=len(failed)
    report['status']='passed' if not failed and (not report['statementChecks'] or report['statementChecks']['status']=='passed') else 'failed'
    report['allModulesChecked']=len(selected)==len(byname);write(output/'result.json',report)
    emit({'event':'verification-finished',**{k:v for k,v in report.items() if k!='moduleResults'},'reportSha256':sha(output/'result.json')});return 0 if report['status']=='passed' else 1


def statement_gates(checks,byname,audits,root,output,lib,lean,flags,run):
    ref_name=checks['referenceModule'];bridge_name=checks['bridgeModule'];reference=inside(byname[ref_name]['path']);bridge=inside(byname[bridge_name]['path'])
    ref_rows={r['name']:r for r in audits[ref_name]['audit']['declarations']};bridge_rows={r['name']:r for r in audits[bridge_name]['audit']['declarations']}
    for name in checks['nonvacuity']:
        if ref_rows[name]['kind']!='theorem':raise ValueError('Missing nonvacuity theorem')
    for claim in checks['claims']:
        row=bridge_rows[claim['bridge']]
        if row['kind']!='theorem' or row['type'].strip()!=claim['reference']:raise ValueError('Bridge does not prove exact specified proposition')
    result={'status':'passed','nonvacuity':checks['nonvacuity'],'claims':checks['claims'],'negativeControls':[]};original=reference.read_text(encoding='utf-8')
    for mutation in checks['negativeMutations']:
        folder=output/'controls'/mutation['name']
        shutil.copytree(lib/'GD',folder/'GD')
        source=folder/byname[ref_name]['path']
        for artifact in source.parent.glob(source.stem+'.*'):
            if artifact.is_file():artifact.unlink()
        source.write_text(original.replace(mutation['old'],mutation['new']),encoding='utf-8');obj=source.with_suffix('.olean')
        compilation=run([str(lean),*flags,'--root='+str(folder),'-o',str(obj),str(source)],folder/'reference.log',[folder])
        reference_diagnostic=(folder/'reference.log').read_text(encoding='utf-8',errors='replace')
        emit({'event':'statement-control-reference','name':mutation['name'],'sourceSha256':sha(source),'compile':compilation,'diagnostic':reference_diagnostic})
        if compilation['exitCode']!=0:raise ValueError('Control specification did not compile')
        rejection=run([str(lean),*flags,'--root='+str(root),str(bridge)],folder/'bridge.log',[folder]);diagnostic=(folder/'bridge.log').read_text(encoding='utf-8')
        emit({'event':'statement-control-bridge','name':mutation['name'],'projectPath':str(folder),'bridge':rejection,'diagnostic':diagnostic})
        if rejection['exitCode'] in (None,0) or not any(s in diagnostic for s in ['Type mismatch','type mismatch','unsolved goals','Application type mismatch']):
            raise ValueError(
                'Changed specification was not rejected for a type/proof error: '
                + mutation['name']
                + '; exitCode=' + repr(rejection['exitCode'])
                + '; diagnostic=' + diagnostic[-4000:]
            )
        result['negativeControls'].append({'name':mutation['name'],'status':'rejected','sourceSha256':sha(source),'compile':compilation,'bridge':rejection,'diagnostic':diagnostic})
    folder=output/'controls/extra-axiom';folder.mkdir(parents=True);source=folder/'Injected.lean';proposition=checks['axiomControlReference']
    source.write_text(f'import {ref_name}\naxiom injected : {proposition}\ntheorem forged : {proposition} := injected\n',encoding='utf-8')
    compile_result=run([str(lean),'--root='+str(folder),'-o',str(source.with_suffix('.olean')),str(source)],folder/'compile.log',[folder,lib]);audit_result=run([str(lean),'--run',str(root/'tools/AuditModule.lean'),'Injected'],folder/'audit.json',[folder,lib])
    if compile_result['exitCode']!=0 or audit_result['exitCode']!=0:raise ValueError('Axiom control could not execute')
    audit=read(folder/'audit.json');rows={r['name']:r for r in audit['audit']['declarations']}
    if audit['audit']['nonstandard_axioms']!=['injected'] or rows['forged']['nonstandard_axioms']!=['injected']:raise ValueError('Injected axiom not found in forged theorem')
    try:validate_audit(audit,'Injected')
    except ValueError as error:
        if str(error)!='Disallowed owned/imported axioms':raise
    else:raise ValueError('Injected axiom passed policy')
    result['negativeControls'].append({'name':'extra-axiom','status':'rejected','sourceSha256':sha(source),'compile':compile_result,'auditExecution':audit_result,'ownedAudit':audit})
    return result

if __name__=='__main__':
    try:sys.exit(main())
    except Exception as error:emit({'event':'verification-error','status':'failed','error':str(error)});sys.exit(1)
