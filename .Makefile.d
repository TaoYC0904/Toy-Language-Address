lib/RTClosure.vo lib/RTClosure.glob lib/RTClosure.v.beautified lib/RTClosure.required_vo: lib/RTClosure.v 
lib/RTClosure.vio: lib/RTClosure.v 
lib/RTClosure.vos lib/RTClosure.vok lib/RTClosure.required_vos: lib/RTClosure.v 
Imp.vo Imp.glob Imp.v.beautified Imp.required_vo: Imp.v lib/RTClosure.vo
Imp.vio: Imp.v lib/RTClosure.vio
Imp.vos Imp.vok Imp.required_vos: Imp.v lib/RTClosure.vos
Language.vo Language.glob Language.v.beautified Language.required_vo: Language.v Imp.vo
Language.vio: Language.v Imp.vio
Language.vos Language.vok Language.required_vos: Language.v Imp.vos
Embeddings.vo Embeddings.glob Embeddings.v.beautified Embeddings.required_vo: Embeddings.v Imp.vo Language.vo
Embeddings.vio: Embeddings.v Imp.vio Language.vio
Embeddings.vos Embeddings.vok Embeddings.required_vos: Embeddings.v Imp.vos Language.vos
