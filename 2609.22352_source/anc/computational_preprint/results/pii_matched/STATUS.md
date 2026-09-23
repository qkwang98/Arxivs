# Aborted Before Comparison

The first attempt to load reusable results stopped because a numeric JSON
key `0.0` was parsed as an integer. No comparison was performed here.
The loader was corrected; the follow-up is in `../pii_comparison/`.
