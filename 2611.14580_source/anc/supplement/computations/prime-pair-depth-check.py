"""Exhaustively verify the finite prime-pair condition used for depth bounds.

Requires Python 3.10+ and its standard library. Default limit: 20,000,000.
Only the chosen report is written; the expected summary is never modified.
"""
import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
import struct
from time import perf_counter


DEFAULT_LIMIT = 20_000_000


def check(limit):
    prime = bytearray(b'\x01') * (limit + 1)
    prime[0:2] = b'\x00\x00'
    for q in range(2, isqrt(limit) + 1):
        if prime[q]:
            first = q * q
            prime[first:limit + 1:q] = b'\x00' * (((limit - first) // q) + 1)
    primes = [p for p in range(3, limit + 1, 2) if prime[p]]
    allowed = primes[1:]  # Excludes 3, starts with 5.
    exceptions = []
    max_least_q = 0
    max_example = None
    digest = hashlib.sha256()
    for index, p in enumerate(primes):
        target = p + 3
        pair = None
        for q in allowed:
            if 2 * q > target:
                break
            r = target - q
            # q >= 5 implies r <= p-2 <= limit, so the sieve contains r.
            if prime[r]:
                pair = (q, r)
                assert 3 < q <= r <= p - 2
                break
        if pair is None:
            exceptions.append(p)
        else:
            q, r = pair
            digest.update(struct.pack('<III', p, q, r))
            if q > max_least_q:
                max_least_q = q
                max_example = [p, q, r]
        if (index + 1) % 250000 == 0:
            print(f'Checked {index + 1} odd primes through {p}; '
                  f'exceptions={exceptions}', flush=True)

    def trial_prime(n):
        return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

    crosscheck = min(limit, 10000)
    assert all(bool(prime[n]) == trial_prime(n) for n in range(crosscheck + 1))
    assert exceptions == [3, 5], f'Unexpected failed prime-pair condition: {exceptions}'
    return {
        'cutoff': limit,
        'odd_prime_count': len(primes),
        'largest_prime': primes[-1],
        'exceptions_including_3_and_5': exceptions,
        'tested_primes_at_least_7': len(primes) - 2,
        'largest_least_first_summand': max_least_q,
        'example_p_q_r_for_largest_least_first_summand': max_example,
        'sha256_ordered_little_endian_uint32_witness_triples': digest.hexdigest(),
        'sieve_crosscheck_trial_division_through': crosscheck,
    }


def main():
    if not __debug__:
        raise SystemExit('Assertions are part of the check; do not use -O or -OO.')
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=DEFAULT_LIMIT,
                        help='inclusive prime bound (default: 20000000)')
    parser.add_argument('--output', type=Path,
                        default=here.parent / 'reports' / 'prime-pair-depth-verification.json',
                        help='mutable report path; expected summary is never overwritten')
    args = parser.parse_args()
    if not 7 <= args.limit <= 2**32 - 1:
        parser.error('--limit must be between 7 and 4294967295')
    expected_path = here / 'prime-pair-depth-expected.json'
    if args.output.resolve() == expected_path.resolve():
        parser.error('--output must not overwrite the expected summary')
    start = perf_counter()
    summary = check(args.limit)
    expected_match = None
    if args.limit == DEFAULT_LIMIT:
        expected = json.loads(expected_path.read_text(encoding='utf-8'))
        assert summary == expected, 'Fresh summary differs from the recorded exact summary'
        expected_match = True
    report = {
        'status': 'PASS',
        'expected_summary_match': expected_match,
        'summary': summary,
        'elapsed_seconds': round(perf_counter() - start, 3),
        'method': 'Eratosthenes sieve; for each odd prime p, scan primes q>=5 '
                  'in increasing order, put r=p+3-q, and test primality of r. '
                  'Repeated summands are allowed. Verify q,r<=p-2 and hash the '
                  'least-q witness (p,q,r) as three little-endian uint32 values.',
        'scope': 'Finite prime-pair condition only. The manuscript turns it into '
                 'depth at most two for variable cutoffs in the verified range. '
                 'This does not compute exact depth, prove the condition beyond '
                 'the tested limit, or prove depth at most two for relation-weight cutoffs.',
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
