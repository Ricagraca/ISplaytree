From iris_time.heap_lang Require Export tactics.

Ltac prim_step :=
  lazymatch goal with
  | |- prim_step ?e _ _ _ _ _ =>
      reshape_expr true e ltac:(fun K e' =>
        esplit with K e' _ ; [ reflexivity | reflexivity | ] ; econstructor
      )
  end.
