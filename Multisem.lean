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
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec1
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec2
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec3
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec4
import Multisem.CaseStudies.VFA.NLSpecs.SortSpec5
--import Multisem.CaseStudies.VFA.SearchTree
import Multisem.CaseStudies.VFA.MultiSet
import Multisem.CaseStudies.VFA.NLSpecs.MultiSetSpec1
import Multisem.CaseStudies.VFA.NLSpecs.MultiSetSpec2
import Multisem.CaseStudies.VFA.NLSpecs.MultiSetSpec3
import Multisem.CaseStudies.VFA.NLSpecs.InsertionSortSpec1
import Multisem.CaseStudies.VFA.NLSpecs.InsertionSortSpec2
import Multisem.CaseStudies.VFA.NLSpecs.InsertionSortSpec3
--import Multisem.Examples.Misc
--import Multisem.Examples.TimeIt

--import Multisem.Difflists
--import Multisem.SearchOrderCheck
