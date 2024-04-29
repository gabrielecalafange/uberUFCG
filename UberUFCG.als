module UberUFCG


abstract sig Usuario {
	agendamento: one Agenda,
	moradia: one Regiao
}
sig Estudante extends Usuario {}
sig Professor extends Usuario {}
sig Servidor extends Usuario {} 



abstract sig Regiao {
}
sig Norte extends Regiao {}
sig Sul extends Regiao {}
sig Leste extends Regiao {}
sig Oeste extends Regiao {} 
sig Centro extends Regiao {} 



sig Carro {
	foi_motorista: one Usuario,
	foi_passageiro: some Usuario
}



sig RegistroContábil {
	tem_crédito: set Usuario,
	está_em_débito: set Usuario
}


abstract sig Agenda {
	corrida: set Carro
}
sig Ida extends Agenda {
}
sig Volta extends Agenda {}



pred umaMoradia [u:Usuario] {
	one u.moradia
}
pred umaCorridaPorVez [u:Usuario] {
	one u.agendamento
}
pred temUmMotorista [c:Carro] {
	one c.foi_motorista
}

fact { 
	all u:Usuario | umaMoradia[u]
	all u:Usuario | umaCorridaPorVez[u]
	all c:Carro | temUmMotorista[c]


  	one Norte {}
 	one Sul {}
  	one Leste {}
 	one Oeste {}
  	one Centro {}
 	one Ida {}
  	one Volta {}
  	one RegistroContábil {}
}

run {} for 5 but exactly 3 Carro
