#!/bin/sh
set -eu

for command_name in sage M2
do
	if ! command -v "$command_name" >/dev/null 2>&1
	then
		printf '%s\n' "missing required command: $command_name" >&2
		exit 127
	fi
done

for script in \
	verify_rank_two_solution_codimension.sage \
	verify_fixed_rank_boundary.sage
do
	sage "$script"
done

for script in \
	verify_rank_two_solution_codimension.m2 \
	verify_fixed_rank_boundary.m2
do
	M2 --script "$script"
done

printf '%s\n' 'ALL ANCILLARY CHECKS PASSED'
