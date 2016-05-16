module Custo

sig abstract Custo{
	abstract double preco();
}

sig Gratis extends Custo{
	double preco(){
		
	}
}

sig Pago extends Custo{
	double preco(){
		
	}

} 
