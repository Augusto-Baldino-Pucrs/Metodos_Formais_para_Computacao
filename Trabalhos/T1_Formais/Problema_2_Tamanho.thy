theory Problema_2_Tamanho
  imports Main
begin

(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO tamanho
  ============================================================

  A função tamanho calcula a quantidade
  de elementos existentes em uma lista.

  Tipo:

    'a list ⇒ nat

  Significa:

    recebe uma lista de qualquer tipo ('a)
    e retorna um número natural (nat)
    representando seu tamanho.
*)

fun tamanho :: "'a list ⇒ nat" where

  (*
    ========================================================
    CASO BASE
    ========================================================

    A lista vazia não possui elementos.

    Portanto:

      tamanho [] = 0
  *)
  "tamanho [] = 0"

| (*
     =======================================================
     CASO RECURSIVO
     =======================================================

     h = cabeça da lista
     t = cauda da lista

     Uma lista da forma:

       h # t

     possui:

       1 elemento (h)
       +
       o tamanho do restante da lista (t)

     Portanto:

       tamanho (h # t)
         =
       Suc (tamanho t)

     Exemplo:

       tamanho [1,2,3]
       =
       Suc (tamanho [2,3])
       =
       Suc (Suc (tamanho [3]))
       =
       Suc (Suc (Suc (tamanho [])))
       =
       Suc (Suc (Suc 0))
       =
       3
   *)
  "tamanho (h # t) = Suc (tamanho t)"


(* CASOS DE TESTE*)

(* Teste 1:   Tamanho da lista vazia. *)
value "tamanho ([]::nat list)"
(* Resultado esperado: 0 *)

(* Teste 2: Lista contendo apenas um elemento. *)
value "tamanho ([10]::nat list)"
(* Resultado esperado: 1 *)

(* Teste 3: Lista contendo vários elementos. *)
value "tamanho ([1,2,3,4,5]::nat list)"
(* Resultado esperado: 5 *)

(* Teste 4:  Lista de strings. Demonstra que a função é genérica e funciona para qualquer tipo. *)
value "tamanho ([''a'', ''b'', ''c'']::string list)"
(* Resultado esperado: 3 *)

(* Teste 5: Lista de valores booleanos. *)
value "tamanho ([True, False, True]::bool list)"
(* Resultado esperado: 3 *)

end