module UberUFCG

abstract sig Usuario {
    	moradia: one Regiao,
   	tem_crédito: lone RegistroContábil,
    	está_em_débito: lone RegistroContábil
} 
	sig Estudante, Professor, Servidor extends Usuario {}
	sig Motorista, Passageiro in Usuario {}


abstract sig Regiao {
}
	one sig Norte, Sul, Centro, Leste, Oeste extends Regiao {}


abstract sig Agenda {
}
	one sig Ida_7h30, Ida_9h30, Ida_13h30, Ida_15h30, 
			Volta_10h00, Volta_12h00, Volta_16h00, Volta_18h00 extends Agenda {}

sig Corrida {
    motorista: one Motorista,
    passageiro: set Passageiro,
    regiao: one Regiao,
    horario: one Agenda

} { #passageiro <= 3}


sig RegistroContábil {
}


pred umaMoradia [u:Usuario] {
    one u.moradia
}

fact { 

	all u:Usuario | umaMoradia[u]
	all disj u:Usuario | no (u.tem_crédito & u.está_em_débito)
	all disj c:Corrida | c.motorista !in c.passageiro

	one RegistroContábil {}	
}

run {} for 5 but exactly 3 Corrida, 4 Usuario
