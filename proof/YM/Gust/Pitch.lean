import YM.Gust.StyleF
set_option autoImplicit false
set_option maxHeartbeats 490000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala QCD QCD.Lat
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n k d:ℕ}{x:Points (m+1)}(hx:x∈conf _)(a:Axis)
local notation "F"=>Factory T n
local notation "S"=> polarM hK hf n
local notation "Hq"=> Clouds hK hf n
local notation "ξ"=> launch hK hf n
variable (n)
lemma estateR: ∃ Y: Spiral.DiffPlan (polarM hK hf n), Y.Derivatives (polarM hK hf n) ∧ Y.Orientation (Clouds hK hf n).spin:=by
       choose Z h using fun a d=> bestow hK hf n a d -- arity adjust
       let Y:Spiral.DiffPlan (S):=⟨fun _=>0,fun d a=> Z a d⟩; have hv:Y.Derivatives (S):=by
              refine ⟨fun d a B m x hx v=> ?_⟩ -- implicit
              let p := Spiral.Ward.expose ∘v; have he : (S).classTokens ∘p=v:=funext fun i=> Spiral.Ward.sends_back _; rw [←he]; refine (h a d B m p x hx).trans (GermD _ ?_) -- direction?
              filter_upwards [(conf_open _).mem_nhds hx] with i hi; exact (pages hK hf p B i hi).symm
       exact ⟨Y,hv,Spiral.WorkD.compat (Hq).smooth (Hq).laws.toSymmetric (Hq).spin Y hv (fun _ _ _=>rfl)⟩
open Tarn.ChargeQ Patria Patria.Gall Patria.Gall.Onyx -- fix
variable {n} (A:Axis×Axis→K.W) (hA:Persona T A)
local notation "L" i:arg j:arg=> A (i,j)
local notation "J"=>Fin (n+1)
-- create one-copy lift even. identity.I
noncomputable def passP (hf:Foil P K T)(n:ℕ)(x:K.W)(h:x∈Col T false): Mater T n where
      u:=none
      v:=Fin.cons x (fun _=> lampU P K)
      mem i := by induction i using Fin.cases<;> first| exact h| exact coinP hf
include hA in
lemma okP (i b): L i b ∈ Col T false:=by rw [hue,tauMod]; simpa only [Bool.false_eq_true,↓reduceIte,one_smul] using hA.tense.parity (i,b)
noncomputable abbrev markR(i j:Axis)(n:ℕ): Mater T n:=passP hf n (L i j) (okP A hA i j)
lemma fitL(i j:Axis): Stay (markR hf A hA i j n) 4:=by
       intro q; induction q using Fin.cases <;> first| exact hA.tense.lv (i,j) | exact ⟨_,hf.unit _ none⟩
-- field real form. transfer by Fees. Use spins with sigma signs. Ch real.C.Core.Lang.
variable (V:Axis×Axis→(Factory T n).Ref 4)(hV:∀ i:Axis×Axis, Fees (launch hK hf n 4 (V i)) (plant (markR hf A hA i.1 i.2 n)))
local notation "R"=> markR hf A hA
noncomputable def shelV (x:(Factory T n).Ref d):= (polarM hK hf n).project d x
variable (u: Fin m→ (Factory T n).Token)
lemma aligns {p q:(Factory T n).Ref d}(h:Fees (launch hK hf n d p) (launch hK hf n d q)): shelV hK hf p=shelV hK hf q:=by
       apply (S).faithfully; funext y; obtain ⟨m,x,v,hx⟩:=y; rw [←(S).through (Hq).laws.toSymmetric (shelV hK hf p) v hx, ←(S).through (Hq).laws.toSymmetric (shelV hK hf q) v hx]; unfold shelV; rw [zoomT _ _ v p x hx,zoomT _ _ v q x hx]; unfold yawn; rw[starts,starts,Fin.comp_cons,Fin.comp_cons]; exact fosters _ _ _ h _
variable (i j:Axis)
include hV
lemma symL: (polarM hK hf n).project _ (V (i,j))=(polarM hK hf n).project _ (V (j,i)):= by
       apply aligns hK hf; refine Fees.hop (hV _) (Fees.hop ?_ (Fees.swap (hV _))); intro M; simp only[once]; apply congr_arg (M none); ext1 k; induction k using Fin.cases <;> first| rfl| exact hA.tense.sym i j
local notation "r" s:arg=> Mater.act hK (fromP s)
set_option maxHeartbeats 880000 in
lemma movedSS (s:Signed): (S).mirror (Hq).spin 4 s ((S).project _ (V (i,j)))=((↑(signT s i*signT s j:ℝ)):ℂ) • ((S).project _ (V (s.perm i,s.perm j))) :=by
       rw [Spiral.Table.mirror_project, ← map_smul]; apply aligns hK hf
       refine Fees.hop (spinning hK hf _ s _ (fromP s)) (Fees.hop (Fees.spin_meets hK (fromP s) (hV _)) ?_)
       let c:ℂ:= ((↑(signT s i*signT s j:ℝ)):ℂ); let f:=R i j n; let g:=R (s.perm i) (s.perm j) n
       change Fees (axisK hK (fromP s) T n (plant f)) (ξ _ (c • (V (s.perm i,s.perm j)))); rw[pin_pl,map_smul]; refine Fees.hop (w:= c • plant g) ?_ (Fees.scale (Fees.swap (hV (s.perm i,s.perm j))) c); intro M; rw[map_smul,once,once]; change M none _=c • M none g.v; let fH:=(r s) f; have hh:fH.v=update g.v 0 (c • g.v 0):=by
            ext1 u; induction u using Fin.cases with
            | zero=>rw[update_self]; exact hA.tense.geo _ _ (fromP s) i j
            | succ i=>rw[update_of_ne i.succ_ne_zero]; exact coinσ (fromP s) hf
       rw[hh, MultilinearMap.map_update_smul,update_eq_self]
local notation "sX"=>Signed.mirror timeAxis
lemma roseK : (S).conj (Hq).spin 4 ((S).project _ (V (i,j)))=(S).project _ (V (i,j)):=by
       rw [Spiral.Table.conj_project]; apply aligns hK hf
       refine Fees.hop (walnut hK hf _ timeAxis) (Fees.hop (Fees.bars hK timeAxis (hV _)) (Fees.hop ?_ (Fees.swap (hV _))))
       intro M; rw[bar_pl,once,once]; apply congr_arg (M none); ext1 u; induction u using Fin.cases with
       | zero=>
           let s:= Signed.mirror timeAxis; let p:= flipC timeAxis; let c:ℂ:= ((↑(signT s i*signT s j:ℝ)):ℂ); have hp:T.spin p (L i j)= c • L i j:= hA.tense.geo p s (couture _) i j
           have h:c • T.adj timeAxis (L i j)=L i j:=congr_fun (hA.real'a timeAxis) (i,j)
           have hh1:c*c=1:=by unfold c s; rw [Complex.ofReal_mul]; exact (mul_mul_mul_comm ..).trans (by rw [Poised.Plans.Stamp.Stair.mirror_sq,Poised.Plans.Stamp.Stair.mirror_sq,mul_one])
           have hF: T.adj timeAxis (L i j)=c • L i j:=by
             calc
               _= c • (c •T.adj timeAxis (L i j)):=by rw [smul_smul,hh1,one_smul]
               _=c • L i j:= congr_arg (fun v=>c • v) h
           change T.spin p (T.adj timeAxis (L i j))= L i j; rw [hF,map_smul,hp,smul_smul,hh1,one_smul]
       | succ t=> change Ch T timeAxis (lampU P K)=lampU P K; change T.spin _ (T.adj _ (lampU P K))= _; rw [coinL hf timeAxis,coinσ (couture _) hf]
end YM.Massive.Gust
#print axioms YM.Massive.Gust.estateR
#print axioms YM.Massive.Gust.movedSS
#print axioms YM.Massive.Gust.roseK
