#!/usr/bin/env python3
"""Check the current release inventory and portable Markdown links (no Lean execution)."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {'.git', '.lake', '.build', '__pycache__'}


def fail(message):
    raise ValueError(message)


def relative_path(value):
    p = PurePosixPath(value)
    if not value or p.is_absolute() or '..' in p.parts or '\\' in value or ':' in value:
        fail('Nonportable release path: ' + value)
    return p


def inventory(root):
    if (root / '.git').exists():
        raw = subprocess.check_output(['git', 'ls-files', '-z'], cwd=root)
        return set(raw.decode('utf-8').rstrip('\0').split('\0')) - {''}
    return {
        p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()
        and not set(p.relative_to(root).parts) & IGNORED
        and not p.relative_to(root).as_posix().startswith('docs/dag/')
        and p.suffix != '.pyc'
    }


def anchors(text):
    result = set(re.findall(r'<a\s+(?:id|name)=[\"\']([^\"\']+)[\"\']', text))
    counts = {}
    for heading in re.findall(r'^#{1,6}\s+(.+?)\s*#*\s*$', text, re.M):
        heading = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', heading)
        slug = ''.join(c for c in heading.lower() if c.isalnum() or c in '-_ ').replace(' ', '-')
        count = counts.get(slug, 0)
        counts[slug] = count + 1
        result.add(slug + ('-' + str(count) if count else ''))
    return result


def check(root):
    manifest = json.loads((root / 'release-manifest.json').read_text(encoding='utf-8'))
    if manifest.get('schemaVersion') != 2:
        fail('Unsupported current release manifest')
    rows = manifest['files']
    expected = {r['path'] for r in rows}
    if len(expected) != len(rows) or len({p.casefold() for p in expected}) != len(rows):
        fail('Duplicate release path')
    actual = inventory(root)
    if actual != expected | {'release-manifest.json'}:
        fail('Inventory mismatch: missing=' + repr(sorted(expected - actual)) + '; extra=' + repr(sorted(actual - expected - {'release-manifest.json'})))
    for row in rows:
        rel = relative_path(row['path'])
        p = root / rel
        if p.is_symlink() or not p.resolve().is_relative_to(root.resolve()):
            fail('Release path is a symlink or escapes root: ' + str(rel))
        data = p.read_bytes()
        if len(data) != row['bytes'] or hashlib.sha256(data).hexdigest() != row['sha256']:
            fail('Hash/size mismatch: ' + str(rel))
    link_count = 0
    for rel in sorted(expected):
        if not rel.endswith('.md') and rel != 'LICENSE':
            continue
        p = root / rel
        text = p.read_text(encoding='utf-8')
        for target in re.findall(r'!?\[[^\]\n]*\]\(([^)\n]+)\)', text):
            target = target.strip().split(' "', 1)[0].strip('<>')
            parts = urlsplit(target)
            if parts.scheme or parts.netloc:
                continue
            if parts.path.startswith('/'):
                fail('Nonportable Markdown link in ' + rel + ': ' + target)
            dest = (p.parent / unquote(parts.path)).resolve() if parts.path else p.resolve()
            if not dest.is_relative_to(root.resolve()):
                fail('Markdown link escapes release: ' + rel + ': ' + target)
            dest_rel = dest.relative_to(root.resolve()).as_posix()
            if dest_rel not in actual:
                fail('Missing Markdown link: ' + rel + ': ' + target)
            if parts.fragment and dest.suffix == '.md':
                if unquote(parts.fragment) not in anchors(dest.read_text(encoding='utf-8')):
                    fail('Missing Markdown anchor: ' + rel + ': ' + target)
            link_count += 1
    return {'status': 'passed', 'files': len(rows), 'markdownLinks': link_count,
            'scope': 'Exact current file inventory, SHA-256, byte counts and local Markdown targets; no Lean execution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.root.resolve()), indent=2))
        return 0
    except (ValueError, OSError, KeyError) as error:
        print(json.dumps({'status': 'failed', 'error': str(error)}, indent=2))
        return 1


if __name__ == '__main__':
    sys.exit(main())
