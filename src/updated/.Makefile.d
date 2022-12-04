src/Basics.vo src/Basics.glob src/Basics.v.beautified src/Basics.required_vo: src/Basics.v 
src/Basics.vio: src/Basics.v 
src/Basics.vos src/Basics.vok src/Basics.required_vos: src/Basics.v 
src/ExpSyntax.vo src/ExpSyntax.glob src/ExpSyntax.v.beautified src/ExpSyntax.required_vo: src/ExpSyntax.v src/Basics.vo
src/ExpSyntax.vio: src/ExpSyntax.v src/Basics.vio
src/ExpSyntax.vos src/ExpSyntax.vok src/ExpSyntax.required_vos: src/ExpSyntax.v src/Basics.vos
src/Exceptions.vo src/Exceptions.glob src/Exceptions.v.beautified src/Exceptions.required_vo: src/Exceptions.v src/ExpSyntax.vo
src/Exceptions.vio: src/Exceptions.v src/ExpSyntax.vio
src/Exceptions.vos src/Exceptions.vok src/Exceptions.required_vos: src/Exceptions.v src/ExpSyntax.vos
src/Equalities.vo src/Equalities.glob src/Equalities.v.beautified src/Equalities.required_vo: src/Equalities.v src/ExpSyntax.vo
src/Equalities.vio: src/Equalities.v src/ExpSyntax.vio
src/Equalities.vos src/Equalities.vok src/Equalities.required_vos: src/Equalities.v src/ExpSyntax.vos
src/Auxiliaries.vo src/Auxiliaries.glob src/Auxiliaries.v.beautified src/Auxiliaries.required_vo: src/Auxiliaries.v src/Exceptions.vo src/SideEffects.vo src/Equalities.vo
src/Auxiliaries.vio: src/Auxiliaries.v src/Exceptions.vio src/SideEffects.vio src/Equalities.vio
src/Auxiliaries.vos src/Auxiliaries.vok src/Auxiliaries.required_vos: src/Auxiliaries.v src/Exceptions.vos src/SideEffects.vos src/Equalities.vos
src/SideEffects.vo src/SideEffects.glob src/SideEffects.v.beautified src/SideEffects.required_vo: src/SideEffects.v src/ExpSyntax.vo
src/SideEffects.vio: src/SideEffects.v src/ExpSyntax.vio
src/SideEffects.vos src/SideEffects.vok src/SideEffects.required_vos: src/SideEffects.v src/ExpSyntax.vos
src/Scoping.vo src/Scoping.glob src/Scoping.v.beautified src/Scoping.required_vo: src/Scoping.v src/ExpSyntax.vo
src/Scoping.vio: src/Scoping.v src/ExpSyntax.vio
src/Scoping.vos src/Scoping.vok src/Scoping.required_vos: src/Scoping.v src/ExpSyntax.vos
src/Manipulation.vo src/Manipulation.glob src/Manipulation.v.beautified src/Manipulation.required_vo: src/Manipulation.v src/Scoping.vo
src/Manipulation.vio: src/Manipulation.v src/Scoping.vio
src/Manipulation.vos src/Manipulation.vok src/Manipulation.required_vos: src/Manipulation.v src/Scoping.vos
src/ScopingLemmas.vo src/ScopingLemmas.glob src/ScopingLemmas.v.beautified src/ScopingLemmas.required_vo: src/ScopingLemmas.v src/Manipulation.vo
src/ScopingLemmas.vio: src/ScopingLemmas.v src/Manipulation.vio
src/ScopingLemmas.vos src/ScopingLemmas.vok src/ScopingLemmas.required_vos: src/ScopingLemmas.v src/Manipulation.vos
src/Frames.vo src/Frames.glob src/Frames.v.beautified src/Frames.required_vo: src/Frames.v src/ScopingLemmas.vo
src/Frames.vio: src/Frames.v src/ScopingLemmas.vio
src/Frames.vos src/Frames.vok src/Frames.required_vos: src/Frames.v src/ScopingLemmas.vos
src/SubstSemantics.vo src/SubstSemantics.glob src/SubstSemantics.v.beautified src/SubstSemantics.required_vo: src/SubstSemantics.v src/Frames.vo src/Exceptions.vo src/Auxiliaries.vo
src/SubstSemantics.vio: src/SubstSemantics.v src/Frames.vio src/Exceptions.vio src/Auxiliaries.vio
src/SubstSemantics.vos src/SubstSemantics.vok src/SubstSemantics.required_vos: src/SubstSemantics.v src/Frames.vos src/Exceptions.vos src/Auxiliaries.vos
src/Termination.vo src/Termination.glob src/Termination.v.beautified src/Termination.required_vo: src/Termination.v src/SubstSemantics.vo
src/Termination.vio: src/Termination.v src/SubstSemantics.vio
src/Termination.vos src/Termination.vok src/Termination.required_vos: src/Termination.v src/SubstSemantics.vos
src/SubstSemanticsLemmas.vo src/SubstSemanticsLemmas.glob src/SubstSemanticsLemmas.v.beautified src/SubstSemanticsLemmas.required_vo: src/SubstSemanticsLemmas.v src/SubstSemantics.vo
src/SubstSemanticsLemmas.vio: src/SubstSemanticsLemmas.v src/SubstSemantics.vio
src/SubstSemanticsLemmas.vos src/SubstSemanticsLemmas.vok src/SubstSemanticsLemmas.required_vos: src/SubstSemanticsLemmas.v src/SubstSemantics.vos
src/CIU.vo src/CIU.glob src/CIU.v.beautified src/CIU.required_vo: src/CIU.v src/Termination.vo
src/CIU.vio: src/CIU.v src/Termination.vio
src/CIU.vos src/CIU.vok src/CIU.required_vos: src/CIU.v src/Termination.vos
src/CTX.vo src/CTX.glob src/CTX.v.beautified src/CTX.required_vo: src/CTX.v src/CIU.vo
src/CTX.vio: src/CTX.v src/CIU.vio
src/CTX.vos src/CTX.vok src/CTX.required_vos: src/CTX.v src/CIU.vos
src/LogRel.vo src/LogRel.glob src/LogRel.v.beautified src/LogRel.required_vo: src/LogRel.v src/Termination.vo src/Equalities.vo
src/LogRel.vio: src/LogRel.v src/Termination.vio src/Equalities.vio
src/LogRel.vos src/LogRel.vok src/LogRel.required_vos: src/LogRel.v src/Termination.vos src/Equalities.vos
