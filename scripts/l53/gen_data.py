# SPDX-License-Identifier: Apache-2.0
"""Validate representative certificates and write compact data lines: 'c0 c1 ... | m1 k1 m2 k2 ...'."""
import itertools, json, sys
def add(a, b):
    return sum(((((a >> (2*i)) & 3) + ((b >> (2*i)) & 3)) & 3) << (2*i) for i in range(3))
def check(t, seq, cert):
    n = len(seq)
    for E, _ in cert:
        if E == 0 or E >> n: return False
        s = 0
        for i in range(n):
            if E >> i & 1: s = add(s, seq[i])
        if s: return False
    rows = [0] + [1 << j for j in range(n)] + ([(1 << j) | (1 << k) for j, k in itertools.combinations(range(n), 2)] if t >= 2 else [])
    return all(sum(c for E, c in cert if E & J == J) == (1 if J == 0 else 0) for J in rows)
def main():
    out = {}
    hnf1 = {}
    none = [list(map(int, l.split())) for l in open('reps14_none.txt')]
    for i, seq in enumerate(none):
        hnf1[tuple(seq)] = [tuple(x) for x in json.load(open(f'hnf/t1_{i}.json'))]
    lines14 = []
    for line in open('reps14_certs.txt'):
        codes, cert = line.split('|')
        seq = list(map(int, codes.split()))
        cert = cert.strip()
        if cert == 'NONE':
            c = hnf1[tuple(seq)]
        else:
            pos, neg = cert.split(';')
            c = [(int(m), 1) for m in pos.split()] + [(int(m), -1) for m in neg.split()]
        assert check(1, seq, c), seq
        lines14.append(' '.join(map(str, seq)) + ' | ' + ' '.join(f'{m} {k}' for m, k in c))
    lines18 = []
    for line in open('reps18_certs.txt'):
        codes, cert = line.split('|')
        seq = list(map(int, codes.split()))
        v = list(map(int, cert.split()))
        c = list(zip(v[0::2], v[1::2]))
        assert check(2, seq, c), seq
        lines18.append(' '.join(map(str, seq)) + ' | ' + ' '.join(f'{m} {k}' for m, k in c))
    open('data14.txt', 'w').write('\n'.join(lines14) + '\n')
    open('data18.txt', 'w').write('\n'.join(lines18) + '\n')
    print(len(lines14), len(lines18), 'all certificates verified')
main()
