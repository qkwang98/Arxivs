# Endpoint diagnostics, not the final comparison

The original continuation stopped at the monitor accuracy gate at t=8.
The spectral settings from the first-pulse study produced a reference
Stokes-variation drift of 2.52e-6 in the most sensitive row.

The unmodified contour settings (tolerance 1e-14, order 40) produced
a relative solution error of 1.91e7 and a column-direction error of 0.548.
These results are retained in results.json and contour_endpoint_probe.json.
They are failures of this numerical configuration, not physical changes
of the monodromy invariants.

endpoint_refined.json records an intermediate monitor with tolerance 1e-42.
endpoint_checked.json records the subsequent tighter endpoint calculation.
The completed interval comparison is stored separately.
