module Aplicativo

sig Aplicativo{
	custo: one Custo,
	status: one Status,
	versoes: some VersaoAplicativo,
	acoes: some 
}
