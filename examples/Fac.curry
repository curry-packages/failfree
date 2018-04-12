faci n = if n==0 then 1 else n * faci (n-1)

facg'nonfail n = n>=0

facg n | n==0 = 1
       | n>0  = n * facg (n-1)
       