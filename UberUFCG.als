module UberUFCG

abstract sig Usuario {
    moradia: one Regiao
} 


sig Estudante, Professor, Servidor extends Usuario {}
sig Motorista, Passageiro in Usuario {}

sig Debito in Passageiro {}
sig Credito in Motorista {}

abstract sig Regiao {}
one sig Norte, Sul, Centro, Leste, Oeste extends Regiao {}

abstract sig Agenda {}
one sig Ida_7h30, Ida_9h30, Ida_13h30, Ida_15h30, 
		Volta_10h00, Volta_12h00, Volta_16h00, Volta_18h00 
			extends Agenda {}


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


pred umaMoradia [u:Usuario] {
    one u.moradia
}

pred mesmaHora[c1, c2: Corrida] {
    c1 != c2 => c1.horario != c2.horario
}


fact { 

    	all u:Usuario | umaMoradia[u]

 	all p:Passageiro | one d:Debito | d in p 

	all m:Motorista | one c:Credito | c in m

   	all disj c1, c2: Corrida | 
		mesmaHora[c1, c2] && c1.motorista != c2.motorista && c1.passageiro != c2.passageiro 
}

run {} for 5 but exactly 4 Corrida, 7 Usuario
