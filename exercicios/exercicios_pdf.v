(* Cria seções lógicas, separando o escopo das variáveis e melhorando a organização*)
Section ex1. 
    Variables p q: Prop.

    Lemma der_ex1: (p -> p -> q) -> p -> q.
    (* Inicia provas *)
    Proof.
        (* Faz a técnica de introdução da implicação. *)
        (* Na prática, insere o contexto na linha de cima. No caso, joga a parte esquerda da implicação para cima como uma hipótese. *)
        (*É possível dar nomes às hipóteses*)
        (* intro hipotese_h1.  *)
        (* intro hipotese_h2. *)
        (* Ao invés de dar vários intro, é possível fazer todos os possíveis de uma vez usando intros.*)
        intros.
        apply H.
        - exact H0.
        - assumption.
    (* Termina provas *)
    Qed.
End ex1.

Section ex2.
    Variables p q r t: Prop.

    Lemma ex2: (q -> r -> t) -> (p -> q) -> p -> r -> t.
    Proof.
        intros H1 H2 H3.
        apply H1. apply H2. apply H3.
    Qed.
End ex2.