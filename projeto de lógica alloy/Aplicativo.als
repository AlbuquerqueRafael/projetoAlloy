module Aplicativo

sig Aplicativo{
	custo: one Custo,
	versoes: some VersaoAplicativo,
	acoes: some AcoesComUmAplicativo,
}

pred Instalado [a:Aplicativo] {}

pred NaoInstalado [a:Aplicativo] {}
