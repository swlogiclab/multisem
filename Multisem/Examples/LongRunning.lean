import Multisem.Examples.Misc
-- some longer-running examples
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
theorem misc4 : pspec [| every natural is nonnegative and is even or odd |] :=
  by simp
--@[simp]
--def every_natural_is_nonneg_and_even_or_odd := (pspec ("every" # ("natural" # ("is" # ("non-negative" # ("and" # ("is" # ("even"#("or"#"odd")))))))))
--theorem misc4 : every_natural_is_nonneg_and_even_or_odd :=
--  by simp
