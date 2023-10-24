/**
Três fazendeiros que compartilharam uma mula por um
tempo discutem quem é o verdadeiro dono do animal.
No entanto, pessoalmente nenhum deles quer se
responsabilizar pela mula. Os três fazem as seguintes
declarações, em que uma é verdadeira e outra é falsa.

A
1. A mula é de C.
2. Não posso ser o dono.
B
1. C não é o dono.
2. A mula é de A.
C
1. A mula é minha.
2. A segunda declaração de B é falsa
De quem é a mula, afinal?
*/

abstract sig Fazendeiros {}
sig Dono in Fazendeiros {}
one sig A, B, C extends Fazendeiros {}
pred dono[d:Dono] {d in Dono}
pred A1 {C in Dono}
pred A2 {A not in Dono}
pred B1 {C not in Dono} 
pred B2 {A in Dono}
pred C1 {C in Dono}
pred C2 {!B2}

fact "restricoes do problema" {
    one x:Dono | dono[x]
    (A1 and !A2) or (!A1 and A2)
    (B1 and !B2) or (!B1 and B2)
    (C1 and !C2) or (!C1 and C2)
}

run {}