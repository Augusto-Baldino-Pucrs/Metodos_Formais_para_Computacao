theory Problema_5_ArvBin
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
  DEFINIÇÃO DA FUNÇÃO cat
  ============================================================

  A função cat concatena duas listas.
*)

fun cat :: "'a list ⇒ 'a list ⇒ 'a list" where
  "cat [] l = l"
| "cat (h # t) l = h # cat t l"


(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO conteudo
  ============================================================

  A função conteudo transforma uma árvore binária
  em uma lista contendo todos os elementos da árvore.

  Tipo:

    'a arvbin ⇒ 'a list

  Significa:

    recebe uma árvore binária
    e retorna uma lista contendo
    todos os valores armazenados nela.
*)

fun conteudo :: "'a arvbin ⇒ 'a list" where

  (*
    ========================================================
    CASO BASE
    ========================================================

    A árvore vazia não possui elementos.

    Portanto:

      conteudo Vazia = []
  *)
  "conteudo Vazia = []"

| (*
     =======================================================
     CASO RECURSIVO
     =======================================================

     Considere a árvore:

         No L x R

     onde:

       L = subárvore esquerda
       x = valor armazenado
       R = subárvore direita

     O conteúdo da árvore é:

       valor da raiz
       seguido do conteúdo da esquerda
       seguido do conteúdo da direita

     Portanto:

       conteudo (No L x R)
         =
       x # cat (conteudo L) (conteudo R)
   *)
  "conteudo (No L x R)
      = x # cat (conteudo L) (conteudo R)"

(* CASOS DE TESTE *)

(* Teste 1: conteúdo da árvore vazia *)
value "conteudo (Vazia :: nat arvbin)"
(* Resultado esperado: [] *)

(* Teste 2: árvore contendo apenas a raiz *)
value "conteudo ((No Vazia 10 Vazia) :: nat arvbin)"
(* Resultado esperado: [10] *)

(* Teste 3: árvore com três nós *)
value "conteudo
        ((No (No Vazia 1 Vazia)
             2
             (No Vazia 3 Vazia))
         :: nat arvbin)"
(* Resultado esperado: [2,1,3] *)

(* Teste 4: árvore maior *)
value "conteudo
        ((No
            (No (No Vazia 1 Vazia)
                2
                Vazia)
            3
            (No Vazia 4 Vazia))
         :: nat arvbin)"
(* Resultado esperado: [3,2,1,4] *)

(* Teste 5: árvore somente à esquerda *)
value "conteudo
        ((No
            (No
                (No Vazia 1 Vazia)
                2
                Vazia)
            3
            Vazia)
         :: nat arvbin)"
(* Resultado esperado: [3,2,1] *)

(* Teste 6: árvore somente à direita *)
value "conteudo
        ((No
            Vazia
            1
            (No
                Vazia
                2
                (No Vazia 3 Vazia)))
         :: nat arvbin)"
(* Resultado esperado: [1,2,3] *)

end