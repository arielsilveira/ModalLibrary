# TCC

### Problemas atuais
 - Retirar os mundos que não existem quando é dito que há uma formula nele

Desenvolvimento futuro 

- Descobrir como construir

- Theorem test : 1 <> 2. 
- Começar a construção de um modelo 
- Começar o desenvolvimento de mundos 
- Rever as anotações criadas pela Kaqui 
- Uma proposição vai ter uma lista de mundos 
- Ver como funciona a construção do Ltac 
- Saber como construir uma fórmula modal 
- Modelar os diferentes sistemas (K, B, D, T, 4, 5...) 
- Diferentes propriedades de cada um modelo, dessa forma
será visto cada uma das restrições. Página 29 
- Provar cada metapropriedade do capítulo 2.4 
- Regras: De Morgan, Necessitação e Axiomas 

### Definição de proposição com mundo

    P -> 2^w
    p0 -> []
    p1 -> [w2, w4]
    p2 -> [w1, w3]


- Comando Compute para ver se esta funcionando o Ltac 
- https://github.com/coq/coq/wiki/Ltac 
- https://coq.inria.fr/refman/proof-engine/ltac.html#grammar-token-cpattern 

### Pontos importantes

- Rever IndProp -> Diferença entre (r: list ...) (w w1 : ...) para list Rel -> world -> world -> Prop
- Definir a relação como World -> World -> Prop
