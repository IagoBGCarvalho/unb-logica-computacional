(* Fixpont é para a definição de funções recursivas *)
Fixpoint fun_soma_impares (n: nat) : option nat :=
    match n with
    | 0 => None
    | S n => match (fun_soma_impares n) with
            | None => Some 1
            | Some k => Some (k + (2 * n - 1))
            end
    end.

Eval compute in fun_soma_impares 1.
Eval compute in fun_soma_impares 2.

Theorem fun_soma_impares_correct: forall n, fun_soma_impares n = Some (n * n).
Proof.
    induction n as [j k].
    - simpl. reflexivity.
    - simpl fun_soma_impares.
rewrite IHK. lia.
Qed.