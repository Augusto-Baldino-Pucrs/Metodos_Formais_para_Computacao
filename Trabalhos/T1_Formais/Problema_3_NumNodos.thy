theory Problema_3_NumNodos
  imports Main
begin

(*
  ============================================================
  DEFINIÇÃO DO TIPO arvbin
  ============================================================

  Uma árvore binária pode ser:

  • Vazia
  • Um nó contendo:
      - subárvore esquerda
      - valor armazenado
      - subárvore direita
*)

datatype 'a arvbin =
    Vazia
  | No "'a arvbin" 'a "'a arvbin"


(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO numnodos
  ============================================================

  A função numnodos calcula a quantidade
  total de nós existentes em uma árvore binária.

  Tipo:

    'a arvbin ⇒ nat

  Significa:

    recebe uma árvore binária
    e retorna um número natural
    correspondente à quantidade de nós.
*)

fun numnodos :: "'a arvbin ⇒ nat" where

  (*
    ========================================================
    CASO BASE
    ========================================================

    A árvore vazia não possui nós.

    Portanto:

      numnodos Vazia = 0
  *)
  "numnodos Vazia = 0"

| (*
     =======================================================
     CASO RECURSIVO
     =======================================================

     Considere uma árvore:

         No L x R

     onde:

       L = subárvore esquerda
       x = valor armazenado no nó
       R = subárvore direita

     O número total de nós é:

       1                  (nó atual)
       +
       numnodos L         (esquerda)
       +
       numnodos R         (direita)

     Portanto:

       numnodos (No L x R)
         =
       1 + numnodos L + numnodos R
   *)
  "numnodos (No L x R)
      = 1 + numnodos L + numnodos R"


(* CASOS DE TESTE *)

(* Teste 1: Árvore vazia. *)
value "numnodos (Vazia :: nat arvbin)"
(* Resultado esperado: 0 *)

(* Teste 2: Árvore contendo apenas a raiz. *)
value "numnodos ((No Vazia 10 Vazia) :: nat arvbin)"
(* Resultado esperado: 1 *)

(* Teste 3: Árvore com três nós. *)
value "numnodos
  ((No (No Vazia 1 Vazia)
       2
       (No Vazia 3 Vazia))
   :: nat arvbin)"
(* Resultado esperado: 3 *)

(* Teste 4: Árvore maior. *)
value "numnodos
  ((No
      (No (No Vazia 1 Vazia)
          2
          Vazia)
      3
      (No Vazia 4 Vazia))
   :: nat arvbin)"
 (* Resultado esperado: 4*)

end