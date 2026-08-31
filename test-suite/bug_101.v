From Unicoq Require Import Unicoq.

Local Set Implicit Arguments.
Set Primitive Projections.
Module Graph.
  Definition class_of (A : Type) := A -> A -> Type.
  Record t: Type:=
    Pack {
        sort : Type;
        Hom : class_of sort
      }.
  Module ForExport.
    Arguments Hom [_].
    Arguments Pack [sort].
    Coercion sort : t >-> Sortclass.
  End ForExport.
End Graph.
Export Graph.ForExport.

Module TwoGraph.
  Definition mixin_of (A : Graph.t)
    := forall (x y : A), Graph.class_of (Graph.Hom x y).

  Record class_of (A : Type) := Class {
                                    base : Graph.class_of A;
                                    is2graph : mixin_of (Graph.Pack base)
                                  }.

  Structure t := Pack {
                     sort : Type;
                     class : class_of sort;
                   }.

  Definition to_graph (A: t)
    : Graph.t
    :=  Graph.Pack (base (class A)).
  Module ForExport.
    Canonical to_graph.
  End ForExport.
End TwoGraph.
Export TwoGraph.ForExport.
Section test.
  Set Printing All.
  Context (A : TwoGraph.t).
  Context (x y : TwoGraph.sort A).
  Check (@Graph.Hom _ x y).
End test.
