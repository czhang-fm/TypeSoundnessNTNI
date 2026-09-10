# Type Soundness proof for Nontransitive Noninterference

This repository stores a machine-checked soundness proof of a type system for the nontransitive noninterference (NTNI) information flow security property in an imperative programming language using Dafny. The original NTNI security property was defined for a functional programming language augmented with memory access operators, where security policies are expressed as coarse-grained information flow constraints over component-based software. Although subsequent work has extended the NTNI type system, to the best of our knowledge, no prior work has provided a machine-checked soundness proof for type-enforced NTNI (up to September 2026). 

Dafny is a proof assistant designed for the verification of functional, imperative, and object-oriented programming languages, which was developed by Microsoft. Dafny has dependency on Visual Studio (in Windows), dotnet (Linux and MacOS), and Z3 (in all systems). 

Probably the easiest way is to install Dafny as a plug-in for Visual Studio code. Try to search for Dafny at the extension bar on the left-hand side of VS code. This will usually get you a runnable Dafny if you are under Windows. For Linux users, you need to install .NET 6.0 and Z3. You should also have Python 3 installed (which is usually not a problem). For more details you may follow the instructions at https://github.com/dafny-lang/dafny/wiki/INSTALL. Once you have dotnet and Z3, the Dafny VS code plug-in will often just work. Installation for MacOS is similar.  



