module appstore

open util/ordering[Time]

-------------------------- ASSINATURAS --------------------------

sig Time {}


one sig Loja {
	aplicativos: some Aplicativo,
	usuarios: some Usuario
}

abstract sig VersaoDoApp{}
one sig Atual, Antiga extends VersaoDoApp{}

abstract sig Aplicativo {
	versao: VersaoDoApp one -> Time,
}

sig AplicativoPago extends Aplicativo{}
sig AplicativoGratis extends Aplicativo{}

sig Conta {
	cartoes : set Cartao,
	dispositivos: set Dispositivo,
	aplicativosassociados: set Aplicativo  -> Time
}

sig Usuario{
	contas : set Conta
}

sig Dispositivo{

	apps : Status -> Aplicativo -> Time, 
}

sig Cartao {

}

abstract sig Status{}
one sig Instalado, NaoInstalado extends Status{}

-------------------------- FATOS --------------------------

fact resumindo {
#Cartao = 1
}

fact Usuario {	
	// Todo usuario tem zero ou uma conta
	all usuario: Usuario | #(usuario.contas) <=1
	// Todo usuario estar na Loja
	all usuario: Usuario | usuario in Loja.usuarios
}

fact Loja{
	// Toda Loja tem pelo menos um Aplicativo
	all loja: Loja | some loja.aplicativos
}

fact Aplicativo {

	// Todo aplicativo no dispositivo o status é instalado e pertence a uma conta associada
	all aplicativo: Aplicativo, dispositivo: Dispositivo, status: Status, time: Time | 
	aplicativo in status.(dispositivo.apps).time => status = Instalado
	and aplicativo in dispositivo.~dispositivos.aplicativosassociados.time

	// Todo aplicativo pago tem uma conta com cartao
	all aplicativoPago: AplicativoPago,  conta: Conta, time: Time | 
	aplicativoPago in conta.aplicativosassociados.time => some conta.cartoes

	// Todo Aplicativo estar na loja
	all aplicativo: Aplicativo | aplicativo in Loja.aplicativos
}

fact Conta{

	// Toda conta tem um usuario
	all conta: Conta | one conta.~contas
}

fact Dispositivo{

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
	instalaAplicativo[a,c,d,s, pre, pos] or removeAplicativo[a,c,d,s, pre, pos] or atualizaAplicativo[a,c,d,s, pre, pos] 
}

-------------------------- FUNÇÕES --------------------------

fun getAplicativosInstalados[s: Instalado, t: Time, d:Dispositivo] : set Aplicativo {
 	 s.(d.apps).t  & Aplicativo
}

fun getAplicativos[loja:Loja] : set Aplicativo{
	loja.aplicativos & Aplicativo
}

fun getContaDeUsuario[usu:Usuario] : set Conta {
	usu.contas & Conta
}

fun getCartoesDeConta[conta: Conta] : set Cartao {
	conta.cartoes & Cartao
}

fun getDispositivosDeUsuario[usu: Usuario]: set Dispositivo {
	usu.contas.dispositivos & Dispositivo
}

-------------------------- PREDICADOS --------------------------

pred init[t: Time]{

no (Dispositivo.apps).t
all c: Conta | no (c.aplicativosassociados).t

}

pred instalaAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: NaoInstalado, antes, depois: Time ]{
	(a !in s.(d.apps).antes) and (a in c.aplicativosassociados.antes) =>
	s.(d.apps).depois = s.(d.apps).antes + a
}

pred removeAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: Instalado, antes, depois: Time ]{
	(a in s.(d.apps).antes) and (a in c.aplicativosassociados.antes) =>
	(s.(d.apps).depois = s.(d.apps).antes - a) and (a in c.aplicativosassociados.depois)
}

pred atualizaAplicativo[a: Aplicativo , c: Conta, d: Dispositivo, s: Instalado, antes, depois: Time ]{

	(a in s.(d.apps).antes) and (a in c.aplicativosassociados.antes) and a.versao.antes = Antiga => a.versao.depois = Atual
	or
	(a in s.(d.apps).antes) and (a in c.aplicativosassociados.antes) and a.versao.antes = Atual => a.versao.depois = Antiga

}

-------------------------- ASSERT'S --------------------------

assert noAppPagoSemCartao{
	// Verifica se existe aplicativo pago associado a uma conta sem cartao
	!some aplicativo: AplicativoPago, conta:Conta, time: Time
	| aplicativo in conta.aplicativosassociados.time and no conta.cartoes
}

assert noLojaSemApp {
	// Verifica se a loja tem aplicativo
	!some loja: Loja | no loja.aplicativos
}

assert noRemoveAssociacao{
	// Verifica que nenhum aplicativo vinculado a uma conta em um determinado tempo sera desvinculado depois
	!some time1,time2:Time , conta:Conta, aplicativo:Aplicativo
	| aplicativo in conta.aplicativosassociados.time1 and aplicativo !in conta.aplicativosassociados.time2 
}

check noRemoveAssociacao for 10
check noLojaSemApp	for 10
check noAppPagoSemCartao for 10

pred show[]{}
run show for 7 but exactly 3 Conta
