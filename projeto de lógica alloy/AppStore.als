module appstore

open util/ordering[Time]
-------------------------- ASSINATURAS --------------------------

sig Time {}


one sig Loja {
	aplicativos: some Aplicativo,
	usuarios: set Usuario
}

abstract sig Aplicativo {}
sig AplicativoPago extends Aplicativo{}
sig AplicativoGratis extends Aplicativo{}

sig Conta {
	cartoes : set Cartao,
	dispositivos: some Dispositivo,
	aplicativosassociados: set Aplicativo -> Time
}

sig Usuario{
	contas : set Conta
}

sig Dispositivo{
	status : one Status,
	apps : status -> Aplicativo -> Time, 
	//aplicativosinstalados : some Aplicativo
}

one sig Cartao {

}


abstract sig Status{}
one sig Instalado extends Status{}
one sig NaoInstalado extends Status{}


-------------------------- FATOS --------------------------

fact Usuario {	
	// Todo usuario tem zero ou uma conta
	all usuario: Usuario | #(usuario.contas) =< 1
	// Todo usuario estar na Loja
	all usuario: Usuario | usuario in Loja.usuarios
}

fact Loja{
	// Toda Loja tem Aplicativos
	all loja: Loja | some loja.aplicativos
}

fact Aplicativo {
	
	// Todo aplicativo no dispositivo o status é instalado
	all a: Aplicativo, d: Dispositivo, s: Status, t: Time | a in s.(d.apps).t <=> s = Instalado

	// Todo aplicativo instalado estar associado a uma conta de aplicativosassociados
	all a: Aplicativo, d: Dispositivo, s: Status, t: Time | a in s.(d.apps).t => a in d.~dispositivos.aplicativosassociados.t

	// Todo aplicativo pago tem uma conta com cartao
	all a: AplicativoPago,  c: Conta, t: Time| a in c.aplicativosassociados.t => some c.cartoes

	// Todo Aplicativo estar na loja
	all a: Aplicativo | a in Loja.aplicativos
}

fact Conta{
	
	// Em toda conta os aplicativos associados vao ser sempre adicionados, independente do tempo 
	all t, t2: Time, c: Conta | #(c.aplicativosassociados.t) >=  #(c.aplicativosassociados.t2)
	// Toda conta tem um usuario
	all c: Conta | one c.~contas
}

fact Dispositivo{

	all a: Aplicativo, d: Dispositivo, c: Conta, t, t2: Time | a in c.aplicativosassociados.t => a in Instalado.(d.apps).t2
	// Todo dispositivo tem zero ou uma conta
	all d: Dispositivo |  #(d.~dispositivos) <=1

}

fact Cartao{
	// Todo cartao tem uma conta
	all c: Cartao | one c.~cartoes
}

fact traces {
	/*
	* Mudança do comportamento do modelo com o tempo
	*/
	init[first]
	all pre: Time-last| let pos = pre.next|
 	some  c: Conta, d: Dispositivo, a: Aplicativo, s: Status|
	instalarAplicativo[a,c,d,s, pre, pos] 
}

assert nuncaDesinstalado {
	some a: Aplicativo, d: Dispositivo, s: NaoInstalado, t: Time | a in s.(d.apps).t 
}

check nuncaDesinstalado


-------------------------- PREDICADOS --------------------------

pred init[t: Time]{

}

pred instalarAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: Status, antes, depois: Time ]{

}

pred show[]{}

run show for 4 but exactly  3 Aplicativo
