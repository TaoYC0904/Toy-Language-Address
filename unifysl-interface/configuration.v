Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [primitive_connective impp
  ;primitive_connective andp
  ;primitive_connective orp
  ;primitive_connective sepcon
  ;primitive_connective negp
  ;primitive_connective falsep
  ;primitive_connective truep
  ;primitive_connective emp
  ;FROM_impp_TO_multi_imp
  ;FROM_empty_set_TO_empty_context
  ].

Definition how_judgements :=
  [ primitive_judgement provable
  ; FROM_provable_TO_derivable
  ].

Definition transparent_names :=
  [expr:parameter
  ;sepcon:parameter
  ;context:parameter].

Definition primitive_rule_classes :=
  [ provability_OF_impp
  ; provability_OF_andp
  ; provability_OF_sepcon_rule_AS_weak
  ; provability_OF_sepcon_rule_AS_mono
  ; provability_OF_sepcon_falsep_rule
  ].

