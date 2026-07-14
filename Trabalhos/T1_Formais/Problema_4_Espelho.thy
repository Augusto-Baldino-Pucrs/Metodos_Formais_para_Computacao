theory Problema_4_Espelho
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
  DEFINIÇÃO DA FUNÇÃO espelho
  ============================================================

  A função espelho recebe uma árvore binária
  e devolve sua imagem espelhada.

  Tipo:

    'a arvbin ⇒ 'a arvbin

  Significa:

    recebe uma árvore binária
    e retorna outra árvore binária
    com os ramos esquerdo e direito trocados.
*)

fun espelho :: "'a arvbin ⇒ 'a arvbin" where

  (*
    ========================================================
    CASO BASE
    ========================================================

    O espelho de uma árvore vazia
    é a própria árvore vazia.

      espelho Vazia = Vazia
  *)
  "espelho Vazia = Vazia"

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

     O espelho é obtido:

       1. Calculando o espelho da direita
       2. Mantendo o valor x
       3. Calculando o espelho da esquerda

     Assim:

       espelho (No L x R)
         =
       No (espelho R) x (espelho L)

     Exemplo:

            2
           / \
          1   3

     torna-se:

            2
           / \
          3   1
   *)
  "espelho (No L x R)
      = No (espelho R) x (espelho L)"


(* CASOS DE TESTE *)

(* Teste 1: espelho da árvore vazia *)
value "espelho (Vazia :: nat arvbin)"
(* Resultado esperado: Vazia *)

(* Teste 2: árvore contendo apenas a raiz *)
value "espelho ((No Vazia 10 Vazia) :: nat arvbin)"
(* Resultado esperado: No Vazia 10 Vazia *)

(* Teste 3: espelhamento de árvore com três nós *)
value "espelho
        ((No (No Vazia 1 Vazia)
             2
             (No Vazia 3 Vazia))
         :: nat arvbin)"
(*
   Resultado esperado:

         No
           (No Vazia 3 Vazia)
           2
           (No Vazia 1 Vazia)
*)

(* Teste 4: espelhamento de árvore maior *)
value "espelho
        ((No
            (No (No Vazia 1 Vazia)
                2
                Vazia)
            3
            (No Vazia 4 Vazia))
         :: nat arvbin)"
(*
   Resultado esperado:

         No
           (No Vazia 4 Vazia)
           3
           (No Vazia 2 (No Vazia 1 Vazia))
*)

(* Teste 5: aplicar espelho duas vezes *)
value "espelho
        (espelho
          ((No (No Vazia 1 Vazia)
               2
               (No Vazia 3 Vazia))
           :: nat arvbin))"
(*
   Resultado esperado:

         No
           (No Vazia 1 Vazia)
           2
           (No Vazia 3 Vazia)
*)

(* Teste 6: verificação visual da propriedade
   espelho (espelho A) = A *)
value "espelho
        (espelho
          ((No Vazia 42 Vazia)
           :: nat arvbin))"
value "((No Vazia 42 Vazia) :: nat arvbin)"
(* Ambos devem resultar na mesma árvore *)

end