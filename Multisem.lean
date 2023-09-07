import Init.Data.Nat

-- Core
import Multisem.HeytingAlgebras
import Multisem.TemporalLogic
import Multisem.Text.ListMacros
import Multisem.Lexicon

-- Various parsing "backends"; only optimized version is enabled for right now, because while they're not expensive to compile, there are multiple definitions of the [| ... |] macro, and only one can be imported here.
--import Multisem.TreeSynth
--import Multisem.Difflists
--import Multisem.SnocDiffLists
import Multisem.DiffListEncoding


-- Unused experiment unrelated to paper
--import Multisem.Morphisms

-- VFA Sorting case studies
import Multisem.CaseStudies.VFA.Sort

-- Table 1 Example 1
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec1
-- Table 1 Example 2
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec2
-- Table 1 Example 3
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec3
-- Table 1 Example 4
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec4
-- Table 1 Example 5
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec5

import Multisem.CaseStudies.VFA.MultiSet
-- Table 1 Example 6
import Multisem.CaseStudies.VFA.NLSpecs.MultiSetSpec1
-- Table 1 Example 7
import Multisem.CaseStudies.VFA.NLSpecs.MultiSetSpec2

-- This is an example we discuss in the paper, but do not give English for
import Multisem.CaseStudies.VFA.NLSpecs.MultiSetSpec3

-- This is disabled because this is currently the one Lean won't load all the lexicon entries for, for unknown reasons
--Table 1 Example 8
--import Multisem.CaseStudies.VFA.NLSpecs.InsertionSortSpec1

--Table 1 Example 9
import Multisem.CaseStudies.VFA.NLSpecs.InsertionSortSpec2
--Table 1 Example 10
import Multisem.CaseStudies.VFA.NLSpecs.InsertionSortSpec3

--import Multisem.CaseStudies.VFA.NLSpecs.MultiSetSpec4
--import Multisem.Examples.Misc
--import Multisem.Examples.TimeIt

--import Multisem.Difflists
--import Multisem.SearchOrderCheck
