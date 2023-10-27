/*
one
some - acima de 1
lone
set*/
sig Local {
    recursos: set Recurso,
    usuarios: set Usuario
}
//Há uma relação hierárquica nos recursos
//entre um recurso pai e um recurso normal
sig Recurso {
    superior: lone Recurso
}

sig Usuario {
    acessa: set Recurso
}
//para todo local e todo usuário, 
//dois locais não podem compartilhar o mesmo usuário.
fact "usuario nao compartilhado" {
    all u :Usuario | one l:Local | u in l.usuarios
}
//o . lado esquerdo, recursos que estão ligados aos locais l, 
//do lado esquerdo, os locais que estão ligados aos recursos r
fact "recurso nao compartilhado" {
    all r:Recurso | one l:Local | r in l.recursos
}

//checagem se o argumento é válido
assert recursoNaoCompartilhado {
    !(some r:Recurso | #(recursos.r) > 1)
}

fact "usuarios acessam hierarquia"{
    all u:Usuario, r:Recurso |
        r in u.acessa implies inferiores[r] in u.acessa
}

//trazendo todos os recursos que o superior é r
fun inferiores[r:Recurso]: set Recurso {
    {r1:Recurso | r in r1.^superior}
}

//tirar os ciclos do grafo para que o fecho transitivo funcione
//^ cria todas as relações transitivas
//r.^superior = retorna todos os superiores de r
//r not in r.^superior = retorna todos os superiores e friza que r não está relacionado com ele mesmo. 
fact "sem ciclos" {
    all r:Recurso | r not in r.^superior
}

check recursoNaoCompartilhado

run {} for 5 but exactly 2 Local