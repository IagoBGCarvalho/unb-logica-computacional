Require Import Arith. (* Biblioteca para aritmética básica *)
Require Import Lia. (* Biblioteca para usar a tática 'lia' 
   (Linear Integer Arithmetic), que resolve equações algébricas automaticamente. *)

(* Definindo uma função recursiva (Fixpoint) para somar os ímpares.*)
Fixpoint fun_soma_impares (n : nat) : nat :=
  match n with
  | 0 => 0
  | S k => fun_soma_impares k + (2 * k + 1)
  end.

(* A proposição que se quer provar. *)
Theorem soma_impares_quadrado : forall n : nat, fun_soma_impares n = n * n.
Proof.
  (* Introduzindo a variável n e aplicando a tática de indução. 
     Isso gera dois sub-objetivos (subgoals): o caso base e o passo indutivo. 
     'k' é a variável do passo indutivo e 'IH' é a Hipótese de Indução. *)
  intro n.
  induction n as [| k IH].
  
  - (* CASO BASE: n = 0 *)
    (* A tática simpl reduz as expressões computáveis. fun_soma_impares 0 vira 0, e 0 * 0 vira 0. *)
    simpl.
    (* reflexivity resolve objetivos do tipo x = x. *)
    reflexivity.
    
  - (* PASSO INDUTIVO: n = S k (o sucessor de k, ou k+1) *)
    (* simpl vai expandir 'fun_soma_impares (S k)' para 'fun_soma_impares k + (2 * k + 1)'. *)
    simpl.
    
    (* O objetivo atual tem um 'fun_soma_impares k' no meio dele. 
       A hipótese de indução (IH) diz que 'fun_soma_impares k = k * k'.
       Usa-se 'rewrite' para substituir o lado esquerdo da HI pelo lado direito no objetivo. *)
    rewrite IH.
    
    (* Agora a meta é: k * k + (2 * k + 1) = (S k) * (S k).
       A álgebra para provar que k^2 + 2k + 1 = (k+1)^2 pode ser resolvida 
       trivialmente pela tática de decisão linear (lia). *)
    lia.
Qed.