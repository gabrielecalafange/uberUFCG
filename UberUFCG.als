module UberUFCG

abstract sig Usuario {
	agendamento: one Agenda,
	moradia: one Regiao

}

abstract sig Regiao {

}

abstract sig Corrida {
	foi_motorista: one Usuario,
	recebeu_carona: some Usuario
}

sig Agenda {

}

sig Estudante extends Usuario {
}


sig Professor extends Usuario {
}

sig Servidor extends Usuario {
} 


pred umaMoradia [u:Usuario] {
	one u.moradia
}

pred umaCorridaPorVez [u:Usuario] {
	one u.agendamento
}

pred temUmMotorista [c:Corrida] {
	one c.foi_motorista
}

fact { 
	all u:Usuario | umaMoradia[u]
	all u:Usuario | umaCorridaPorVez[u]
	all c:Corrida | temUmMotorista[c]
}

run {} for 5 
