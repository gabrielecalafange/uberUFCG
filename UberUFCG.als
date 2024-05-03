module UberUFCG

abstract sig Usuario {
    moradia: one Regiao,
    tem_crédito: lone RegistroContábil,
    está_em_débito: lone RegistroContábil
} 

sig Estudante, Professor, Servidor extends Usuario {}
sig Motorista, Passageiro in Usuario {}

abstract sig Regiao {}
one sig Norte, Sul, Centro, Leste, Oeste extends Regiao {}

abstract sig Agenda {}
one sig Ida_8h, Ida_10h, Ida_14h, Ida_16h, Volta_10h, Volta_12h, Volta_16h, Volta_18h extends Agenda {}

sig Corrida {
    motorista: one Motorista & Usuario,
    passageiro: set Passageiro & Usuario,
    regiao: one Regiao,
    horario: one Agenda
} { 
    #passageiro <= 3
    motorista.moradia = regiao
    all p: passageiro | p.moradia = regiao
    no p: passageiro | p = motorista
}

sig RegistroContábil {}

pred umaMoradia [u:Usuario] {
    one u.moradia
}

pred mesmaHora[c1, c2: Corrida] {
    c1 != c2 => c1.horario != c2.horario
}

fact { 
    all u:Usuario | umaMoradia[u]
    all disj u:Usuario | no (u.tem_crédito & u.está_em_débito)
    all disj c1, c2: Corrida | mesmaHora[c1, c2] && c1.motorista != c2.motorista && c1.passageiro != c2.passageiro
    one RegistroContábil {}    
}

run {} for 5 but exactly 3 Corrida, 4 Usuario
