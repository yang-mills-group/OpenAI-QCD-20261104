import YM.Gust.AxisG
set_option maxHeartbeats 720000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis MeasureTheory Table Work.A01 Outer Tarn Tarn.Choir Tarn.Choir.Strip UV
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix
variable {K: Choir}{C:Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){n m:ℕ}
variable (A:Axis×Axis→K.W)(hA:Tarn.ChargeQ.Persona T A) (J:Axle K (fun a b=>A (a,b)))
local notation "Jt"=>fun a b=>A (a,b)
include hK hf
noncomputable abbrev ChTag(i:Axis)(x:E4× K.W): E4×K.W:=(x.1,Ch T i x.2)
lemma crowned (s:Strip K)(hx:Strip.distinct s)(j:Axis): tone (s.reverse.map (ChTag (T:=T) j))=star (tone s):=by
       let v:=oppositeS T j s; let z:= flipC j; let t(x:E4× K.W): E4×K.W:= (Ortho.move z.coord x.1,T.spin z x.2); have h: s.reverse.map (ChTag (T:=T) j)=v.map t:=by
            unfold v oppositeS; rw[List.map_map]; congr 1; ext1 x; have hp:Ortho.move z.coord (Ortho.move (Signed.reflect j) x.1)=x.1:=by rw [show z.coord= Signed.reflect j from couture _]; ext1 i; by_cases h:i=j<;>simp [Signed.mirrored,h]
            exact Prod.ext hp.symm rfl
       have hu: tone (v.map t)= K.total _ (Points.move z.coord (locus v)) (T.spin z ∘ pulseTags v):= introduces (fun k:E4 × K.W=> Ortho.move z.coord k.1) (fun k=> T.spin z k.2) v
       rw[h, hu,hf.discrete _ _ (Tarn.Choir.dimV T j _ hx) _ _ (couture j)]; exact hf.starry _ hx _
include hA
lemma stress_eye (j i k:Axis): Ch T j (A (i,k))=A (i,k):=by
       let z:= flipC j; let F:= T.adj j; let t:=A (i,k); let c:ℂ:= ↑(signT (Signed.mirror j) i*signT (Signed.mirror j) k); have hu:c*c=1:=by unfold c; rw[Complex.ofReal_mul]; exact (mul_mul_mul_comm ..).trans (by rw[Poised.Plans.Stamp.Stair.mirror_sq,Poised.Plans.Stamp.Stair.mirror_sq,mul_one])
       have hv:T.spin z t=c • t:= hA.tense.geo z _ (couture _) i k
       have h:c • F t=t:= congr_fun (hA.real'a j) (i,k)
       have he: F t=c • t:=by
            calc
              _= c • (c • F t):=by rw [smul_smul,hu,one_smul]
              _=_ := congr_arg (fun v=> c • v) h
       change T.spin z (F t)=t; rw[he,map_smul,hv,smul_smul,hu,one_smul]
omit hA
variable (p q:Bool)(u v:K.W)(hp:u∈Col T p)(hq:v∈ Col T q)(j:Axis){x:Points 2}(hx:x∈conf 2)
noncomputable def cSign(p q:Bool):ℂ:= if p&&q then -1 else 1
private lemma list_pair (x:Points 2)(u v:K.W): grove K (![u,v]) x= [(x 0,u),(x 1,v)]:=by simp [grove,List.ofFn_succ] -- Foil appears auto vars
private lemma g_mark(b:Bool)(v:K.W)(h:v∈Col T b): markedW T b v:=by unfold markedW; rw [(hue ..).1 h]; cases b <;> simp [tauMod]
include hA hp hq hx
local notation "U"=> Ch T j u
local notation "V"=> Ch T j v
lemma star2 : K.total 2 x (![U,V]) = cSign p q*star (K.total 2 x (![u,v])):=by
       rw [← grooved, ←grooved, list_pair hK hf _ _ _, list_pair hK hf _ _ _]
       have hh: Strip.distinct [(x 0,u),(x 1,v)]:=by rw [← list_pair hK hf x]; exact (garden ..).2 hx
       have hP: Strip.distinct [(x 0,U),(x 1,V)]:=by rw [← list_pair hK hf x]; exact (garden ..).2 hx
       rw [←crowned hK hf _ hh j]; exact (hf.flips [] [] (x 0,U) (x 1,V) p q hP (g_mark hK hf _ _ (chai T hK j _ hp)) (g_mark hK hf _ _ (chai T hK j _ hq)))
lemma star3(x':E4)(b i:Axis)(ht:Points.cons x' x∈conf _): phot (Jt) (![U,V]) x b i x'=cSign p q * star (phot (Jt) (![u,v]) x b i x'):=by
       let z:= A (b,i); let X:=(x',z); let C:=cSign p q
       have h(B A0 :K.W): phot (Jt) (![B,A0]) x b i x'=tone (X::[(x 0,B),(x 1,A0)]):=by unfold phot; rw [←grooved]; congr 1
       have hg(B V0 W:K.W): Strip.distinct ((x',B)::[(x 0,V0),(x 1,W)]):=by
            have h : grove K (Fin.cons B (![V0,W])) (Points.cons x' x)=(x',B)::[(x 0,V0),(x 1,W)]:=by simp [grove, List.ofFn_succ,Points.cons];
            rw[←h]; exact (garden ..).2 ht
       let A':=(x 0,Ch T j u); let B':=(x 1,Ch T j v); have hu: markedW T p U:=g_mark hK hf p _ (chai T hK j _ hp); have hv:markedW T q V:= g_mark hK hf q _ (chai T hK j _ hq)
       have hS:= (show tone [X,A',B']=C*tone [X,B',A'] from hf.flips [X] [] A' B' p q (hg ..) hu hv)
       have ht': Strip.distinct [X,B',A']:=by rw [Strip.spots]; exact ((List.Perm.nodup ((show List.Perm _ [X,B',A'] from List.Perm.cons X (List.Perm.swap _ _ [])).map Prod.fst) ((Strip.spots _).1 (hg z _ _))))
       have hz:markedW T false z:=hA.tense.parity _
       have he: tone [X,B',A']= tone [B',X,A']:=by simpa using (hf.flips [] [A'] X B' false q ht' hz hv)
       have hw: Strip.distinct [B',X,A']:= (spots _).2 ((List.Perm.swap _ _ _ |>.map Prod.fst).nodup ((spots _).1 ht'))
       have hζ: tone [B',X,A']=tone [B',A',X]:=by simpa using (hf.flips [B'] [] X A' false p hw hz hu)
       rw [h,h,hS,he,hζ]; congr 1; have hF:= crowned hK hf _ (hg z u v) j; simpa only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,List.map_cons,List.map_nil,ChTag,show Ch T j z=z from stress_eye hK hf A hA j b i] using hF
end YM.Massive.Gust
#print axioms YM.Massive.Gust.star3
#print axioms YM.Massive.Gust.star2
