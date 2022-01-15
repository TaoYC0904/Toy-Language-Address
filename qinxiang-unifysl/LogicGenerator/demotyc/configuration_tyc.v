Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [ primitive_connective andp;
    primitive_connective orp;
    primitive_connective falsep;
    primitive_connective sepcon;
    primitive_connective wand;
    primitive_connective emp;
    primitive_connective impp;
    primitive_connective iffp;
    FROM_falsep_impp_TO_negp;
    FROM_falsep_impp_TO_truep;
    FROM_impp_TO_multi_imp;
    FROM_andp_TO_iter_andp;
    FROM_sepcon_TO_iter_sepcon;
    FROM_empty_set_TO_empty_context ].

Definition how_judgements :=
  [ primitive_judgement provable;
    FROM_provable_TO_derivable;
    FROM_provable_TO_derivable1;
    FROM_provable_TO_logic_equiv ].

Definition transparent_names :=
  [ expr : parameter;
    sepcon : parameter;
    emp : parameter ].

Definition primitive_rule_classes :=
  [ provability_OF_impp;
    provability_OF_andp;
    provability_OF_orp;
    provability_OF_falsep;
    provability_OF_truep;
    provability_OF_iffp;
    provability_OF_negp;
    provability_OF_iter_andp;
    provability_OF_sepcon_rule;
    provability_OF_wand_rule;
    provability_OF_emp_rule;
    provability_OF_iter_sepcon;
    provability_OF_sepcon_orp_rule;
    provability_OF_sepcon_falsep_rule;
    provability_OF_sepcon_rule_AS_weak;
    derivitive_OF_basic_setting;
    derivitive_OF_finite_derivation;
    derivitive_OF_impp;
    derivitive_OF_andp;
    derivitive_OF_orp;
    derivitive_OF_falsep;
    derivitive_OF_truep;
    derivitive_OF_iffp;
    derivitive_OF_negp ].