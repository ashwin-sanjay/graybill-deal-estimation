"""Check finite/symbolic evidence in an isolated copy; never execute Lean.

The directed enclosure inputs are retained, explicitly marked inputs. This suite
checks their identities and finite consequences, not their integral regeneration.
"""
from pathlib import Path
import argparse,copy,hashlib,importlib.metadata,json,os,platform,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def payload(data,kind):
    result=copy.deepcopy(data)
    keys={"rational":['source_manifest','environment','schema'],
          "normalization":['source','format'],
          "interpolation":['format','node_file_sha256','sinc_script_sha256','checker_sha256','inputScope']}
    for key in keys[kind]:result.pop(key,None)
    return result
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work',required=True,type=Path)
    parser.add_argument('--timeout',type=int,default=1800)
    args=parser.parse_args();work=args.work.resolve()
    if args.timeout<1 or args.timeout>43200:raise ValueError('Timeout must be 1..43200 seconds')
    if work.is_relative_to(ROOT) or ROOT.is_relative_to(work):raise ValueError('Work directory must be outside release')
    if work.exists() and any(work.iterdir()):raise ValueError('Work directory must be empty')
    work.mkdir(parents=True,exist_ok=True)
    stage=work/'package';stage.mkdir()
    shutil.copytree(ROOT/'certificates',stage/'certificates',ignore=shutil.ignore_patterns('__pycache__','verification'))
    (stage/'proofs').mkdir();shutil.copyfile(ROOT/'proofs/Proof0003.md',stage/'proofs/Proof0003.md')
    versions={}
    for line in (stage/'certificates/requirements.txt').read_text().splitlines():
        name,want=line.split('==');versions[name]=importlib.metadata.version(name)
        if versions[name]!=want:raise ValueError('Wrong dependency version: '+name)
    logs=work/'logs';logs.mkdir()
    receipt={'schemaVersion':1,'status':'running','python':platform.python_version(),
      'dependencies':versions,'driverSha256':sha(Path(__file__)),
      'scope':'Fresh finite/symbolic computations on current sources and authenticated retained directed enclosures. No directed integral regeneration or Lean execution.',
      'inputs':{p.relative_to(stage).as_posix():sha(p) for p in sorted(stage.rglob('*')) if p.is_file()},
      'checks':[],'derivedPayloadComparisons':[]}
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONPATH',None)
    def run(name,arguments,cwd=stage,extra_scope=''):
        begin=time.monotonic();command=[sys.executable,'-B',*arguments]
        proc=subprocess.run(command,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=args.timeout)
        raw=proc.stdout.decode('utf-8',errors='replace')
        clean=raw.replace(str(work),'[verification-work]').replace(work.as_posix(),'[verification-work]')
        log=logs/(name+'.log');log.write_text(clean,encoding='utf-8')
        row={'name':name,'command':['python','-B',*arguments],'workingDirectory':cwd.relative_to(stage).as_posix(),
             'exitCode':proc.returncode,'elapsedSeconds':time.monotonic()-begin,'log':'logs/'+log.name,'logSha256':sha(log),'scope':extra_scope}
        receipt['checks'].append(row)
        (work/'result.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(row),flush=True)
        if proc.returncode:raise RuntimeError('Failed '+name+': '+clean[-1500:])
    def path(group,file):return f'certificates/Certificate{group:04d}/{file}'
    before={key:json.loads((stage/path(group,file)).read_text()) for key,group,file in [('rational',2,'Data0001.json'),('normalization',3,'Data0006.json'),('interpolation',3,'Data0008.json')]}
    try:
        run('engine-selftest',[path(3,'Script0002.py'),'--selftest'],extra_scope='Interval arithmetic engine selftest.')
        run('charge-normalization',[path(3,'Script0003.py')],extra_scope='Fresh finite normalization of five retained directed charge columns.')
        run('positive-simplex',[path(3,'Script0004.py'),path(3,'Data0006.json')],extra_scope='Exact rational positive simplex conditional on supplied charge boxes.')
        run('continuum-interpolation',[path(3,'Script0006.py'),path(3,'Data0007.json'),'--output',path(3,'Data0008.json')],extra_scope='Fresh interpolation from the retained 392 directed node enclosures.')
        run('wall-local',[path(3,'Script0010.py'),path(3,'Data0009.json')],extra_scope='Finite 225-cell wall cover and positive lower bound; intervals retained.')
        run('wall-separate',[path(3,'Script0011.py'),path(3,'Data0009.json')],extra_scope='Separate finite wall checker without producer imports; intervals retained.')
        run('eight-tent-symbolic',[path(1,'Script0001.py')],extra_scope='Exact symbolic identities, not physical integral generation.')
        run('two-stage-generation',[path(2,'Script0001.py'),'--write'],extra_scope='Fresh exact rational artifact generation under the current Python environment.')
        run('two-stage-exact-replay',[path(2,'Script0001.py'),'--check'],extra_scope='Exact complete artifact replay including current source hashes.')
        run('two-stage-auxiliary',['-m','unittest','-v','Script0004.py'],cwd=stage/'certificates/Certificate0002',extra_scope='Four auxiliary source-identity, support, packet-floor and schema checks.')
        for kind,group,file in [('rational',2,'Data0001.json'),('normalization',3,'Data0006.json'),('interpolation',3,'Data0008.json')]:
            after=json.loads((stage/path(group,file)).read_text())
            if payload(before[kind],kind)!=payload(after,kind):raise ValueError('Mathematical derived payload differs: '+kind)
            receipt['derivedPayloadComparisons'].append({'kind':kind,'mathematicalPayloadExact':True,'generatedPath':path(group,file),'generatedSha256':sha(stage/path(group,file)),
              'excludedMetadata':{'rational':'source manifest, Python environment and schema identifier','normalization':'current source provenance and format identifier','interpolation':'current checker/input provenance and format identifier'}[kind]})
        # Negative controls for retained/current provenance discrimination.
        sys.path.insert(0,str(stage/'certificates/Certificate0003'))
        from Script0012 import check_binding
        data=json.loads((stage/path(3,'Data0001.json')).read_text());bindings={'script_sha256':stage/path(3,'Script0002.py')}
        tampered=copy.deepcopy(data);tampered['eta']='99'
        fake_fresh=copy.deepcopy(data);fake_fresh['script_sha256']=sha(bindings['script_sha256'])
        rejected=0
        for bad in [tampered,fake_fresh]:
            try:check_binding(bad,bindings)
            except ValueError:rejected+=1
        if rejected!=2:raise ValueError('Retained-input negative control failed')
        receipt['negativeControls']={'modifiedPayloadRejected':True,'falseCurrentProducerClaimRejected':True}
        receipt['status']='passed'
    except Exception as exc:
        receipt['status']='failed';receipt['error']=str(exc).replace(str(work),'[verification-work]')
        raise
    finally:(work/'result.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    return 0
if __name__=='__main__':raise SystemExit(main())
