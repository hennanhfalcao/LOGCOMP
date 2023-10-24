/** O computador ideal para Mariana tem que ser rápido, com boa
memória e compacto. Das quatro marcas que ela viu: Lenovo, Dell,
Apple, Acer, apenas uma delas tem as 3 características ao mesmo
tempo
Sabemos que:
Apenas um deles é o ideal
1. Apenas 3 são rápidos, apenas 2 tem boa memória, apenas um é
compacto.
2. Todas quatro marcas possuem pelo menos uma das características
3. Lenovo e Dell têm a mesma capacidade de memória.
4. Dell e Apple são igualmente rápidos.
5. Apenas um entre Apple e Acer é considerado rápido.
Qual computador Mariana deve comprar? */


//conjunto de computadores
abstract sig Computador {}
// subconjuntos
sig Rapido, BoaMemoria, Compacto in Computador {}
//subconjuntos unitários. O extends é para conjuntos disjuntos
one sig APPLE, DELL, LENOVO, ACER extends Computador {}
//declarando predicados
pred ideal[c:Computador] {
    (c in Rapido) and (c in BoaMemoria) and (c in Compacto)
}

fact "restricoes do problema" {
    //Existe apenas um computador ideal
    one x:Computador | ideal[x]
    
    //Apenas 3 são rápidos, apenas 2 tem boa memória, apenas um é compacto
    (#Rapido=3) and (#BoaMemoria=2) and (#Compacto=1)
    
    //Todas as quatro marcas possuem pelo menos uma caracteristica
    all c:Computador | (c in Rapido) or (c in Compacto) or (c in BoaMemoria)

    //Lenovo e Dell têm a mesma capacidade de memória
    (LENOVO in BoaMemoria) <=> (DELL in BoaMemoria)

    //Dell e Apple são igualmente rápidos
    (DELL in Rapido) <=> (APPLE in Rapido)

    //Apenas um entre Apple e Acer é considerado rápido
    ((APPLE in Rapido) and (ACER not in Rapido)) or ((APPLE not in Rapido) and (ACER in Rapido))
}
run {}