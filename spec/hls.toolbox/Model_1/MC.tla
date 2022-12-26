---- MODULE MC ----
EXTENDS hls, TLC

\* CONSTANT definitions @modelParameterConstants:1Clients
const_167209628676620000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:2REQS
const_167209628676621000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3Servers
const_167209628676622000 == 
{2,3}
----

\* CONSTANT definitions @modelParameterConstants:4Replicas
const_167209628676623000 == 
1
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_167209628676624000 ==
OpListInLimit
----
=============================================================================
\* Modification History
\* Created Tue Dec 27 00:11:26 CET 2022 by leon
