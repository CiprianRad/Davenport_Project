#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Compare the tables stored in `DavenportCompute/Data.lean` with regenerated `data14.txt` and
`data18.txt` (the output of `gen_data.py`).

`Data.lean` stores the lines of `data14.txt` (in blocks `data14_0`, `data14_1`, ...) and of
`data18.txt` (in `data18`) as Lean string literals, wrapped with string gaps.

Usage: python3 extract_data.py <path to DavenportCompute/Data.lean> data14.txt data18.txt
"""
import re
import sys


def tables(lean_source):
    defs = re.findall(r'def (data14_\d+|data18) : String :=\n  "(.*?)"\n', lean_source, re.S)
    text = {name: re.sub(r'\\\n\s*', '', body).replace('\\n', '\n') for name, body in defs}
    blocks = sorted((n for n in text if n.startswith('data14_')), key=lambda n: int(n.split('_')[1]))
    return ''.join(text[n] for n in blocks), text['data18']


def main():
    data14, data18 = tables(open(sys.argv[1], encoding='utf-8').read())
    ok = True
    for name, stored, path in [('data14', data14, sys.argv[2]), ('data18', data18, sys.argv[3])]:
        fresh = open(path, encoding='utf-8').read()
        same = stored.strip('\n') == fresh.strip('\n')
        ok &= same
        print(f'{name}: {len(stored.splitlines())} stored lines, {"identical" if same else "DIFFERENT"}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
