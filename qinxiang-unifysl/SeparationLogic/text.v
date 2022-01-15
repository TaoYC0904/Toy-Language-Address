Require Import Logic.GeneralLogic.Base.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.MinimumLogic.Syntax.

Context {L: Language}
        {minL: MinimumLanguage L}
        {sepconL: SepconLanguage L}
        {Gamma: Provable L}.

Goal forall x y, provable (sepcon x y).