1.5.1:
======

  - Improved performance by avoiding creating and clearing the cache at each run.

1.5:
====

  - Removed dependency to `num` library.
  - Added support for primitive projections.
  - Added new options for controling if to unify types or not during instantiation (experimental, use with care!).
  - Added new primitive `instantiate` for performing instantiation without checking the types (use only if you know types agree!).
