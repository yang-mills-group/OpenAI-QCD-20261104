import YM.Gust.Skilt
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter MeasureTheory Analysis Tarn Tarn.Choir Tarn.Choir.Strip UV Mater Kind Gala
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius ComplexOrder Matrix InnerProductSpace Classical
variable {K: Choir}{C: Sequence}{P:Calibration C}{T:Pollens P K}(hK:K.Domestic)(hf: Foil P K T){m n k d:ℕ}{x:Points (m+1)}(hx:x∈conf _)(a:Axis)
local notation "F"=>Factory T n
local notation "S"=> polarM hK hf n
local notation "Hq"=> Clouds hK hf n
local notation "ξ"=> launch hK hf n
abbrev yawn (v:Fin m→ (Factory T n).Token)(u:(Factory T n).Ref d) (x:Points (m+1)):= (polarM hK hf n).read x (Fin.cons ⟨d,u⟩ v)
lemma fosters (p : Fin m→ Stake T n)(u w:Stake T n) (h: Fees u w)(x: Points (m+1)): valuation T n (m+1) x (Fin.cons u p)=valuation T n (m+1) x (Fin.cons w p):=by
       have ht:=quotes x 0 (Fin.cons (α:=fun _=>Stake T n) 0 p) u w h; simpa only [Fin.update_cons_zero] using ht
variable (v:Fin m→(Factory T n).Token)(u:(Factory T n).Ref d)
include hx
lemma recordJ (i:(Factory T n).Ref (d+1))(h:Fees (launch hK hf n (d+1) i) (leaps hK hf a n (launch hK hf n d u))) : yawn hK hf v i x = Points.gradient 0 a (yawn hK hf v u) x:=by
       let J:= Fin.cons (α:=fun _=> (F).Token) ⟨d,u⟩ v; have ht:= greatness hK hf hx a (stint hK hf ∘v) (launch hK hf n d u)
       let R:= yawn hK hf v u; let y(t):= Ward.cast x 0 a t
       have he(z:Points (m+1))(L)(i:(Factory T n).Ref L): yawn hK hf v i z= valuation T n (m+1) z (Fin.cons (ξ _ i) (stint hK hf∘ v)):=by
              unfold yawn; rw [starts,Fin.comp_cons]
       have hD:HasDerivAt (fun t=> R (y t)) (yawn hK hf v i x) 0:=by unfold R; simp_rw [he]; rw [fosters _ _ _ h]; exact ht
       haveI:ContinuousSMul ℝ (Points (m+1)):= IsBoundedSMul.continuousSMul; have hh:y 0=x:=Ward.start ..; have hw:y 0∈ conf _:=hh.symm ▸ hx; have hf: DifferentiableAt ℝ R (y 0) := (((S).smooth_read (Hq).smooth J).contDiffAt ((conf_open _).mem_nhds hw)).differentiableAt (by simp)
       have hg:= hf.hasFDerivAt.comp_hasDerivAt 0 (show HasDerivAt y (Points.direction 0 a) 0 from Ward.moves ..); rw [hh] at hg; exact hD.unique hg
omit hx
-- ext deriv probe at coordinates raw tags
lemma pages (z:(polarM hK hf n).Field d)(x:Points (m+1))(hx:x∈conf (m+1)): (polarM hK hf n).useAt S x (Fin.cons ⟨d,z⟩ ((S).classTokens ∘ v))= yawn hK hf v ((S).representative d z) x :=by
        have ht:=(S).at_project (S) (Hq).laws.toSymmetric (fun _=>le_rfl) hx (Fin.cons ⟨d,(S).representative d z⟩ v); rw [Fin.comp_cons] at ht; simpa only [Spiral.Table.classTokens,Spiral.Table.rep] using ht -- le_rfl respects
lemma zoomT (x:Points (m+1))(hx:x∈conf (m+1)): (polarM hK hf n).useAt S x (Fin.cons ⟨d,(S).project d u⟩ ((S).classTokens ∘ v))= yawn hK hf v u x:=by
       have ht:=(S).at_project (S) (Hq).laws.toSymmetric (fun _=>le_rfl) hx (Fin.cons ⟨d,u⟩ v); rw [Fin.comp_cons] at ht; exact ht
noncomputable abbrev NoteVel (n d:ℕ) (Q: (polarM hK hf n).Field d)(w: (polarM hK hf n).Field (d+1)) :Prop:= ∀ m:ℕ,∀ v:Fin m→ (Factory T n).Token,∀ x∈ conf (m+1), (polarM hK hf n).useAt (polarM hK hf n) x (Fin.cons ⟨d+1,w⟩ ((polarM hK hf n).classTokens ∘ v))=Points.gradient 0 a (yawn hK hf v ((polarM hK hf n).representative d Q)) x
variable (n)
lemma bestow (d:ℕ):∃ U :(polarM hK hf n).Field d →ₗ[ℂ] (polarM hK hf n).Field (d+1),∀ Q: (polarM hK hf n).Field d, NoteVel hK hf a n d Q (U Q):=by
       have he(u:(polarM hK hf n).Field d):∃ p,NoteVel hK hf a n d u p:=by
             let Q:= (polarM hK hf n).representative _ u; obtain ⟨z,h⟩:= united hK hf _ (lives hK hf a _ (lunar hK hf Q)); exact ⟨(S).project _ z, fun i x k hX=> (zoomT hK hf x z k hX).trans (recordJ hK hf hX a x Q z h)⟩
       choose p hp using he
       refine ⟨{toFun:=p,map_add':=fun i j=>?_,map_smul':=fun c i=>?_},hp⟩
       · apply (S).faithfully; funext x; obtain ⟨m,x,v,hx⟩:=x
         change (S).spectra _ _ _=(S).spectra _ _ _; rw [map_add,Pi.add_apply]; simp_rw [← (S).through (Hq).laws.toSymmetric (d:=d+1) _ v hx, show ∀ u, _= Points.gradient (n:=m+1) 0 a (yawn hK hf v ((S).representative d u)) x from fun u=> hp u m v x hx]
         let g(t:(S).Field d):= yawn hK hf v ((S).representative _ t); have hh: g (i+j)=g i+g j:=by funext z; exact (show _ from map_add (((S).injectFront v z _).comp ((S).representative _)) i j)
         have ht(p:(S).Field d): DifferentiableAt ℝ (g p) x:= (((S).smooth_read (Hq).smooth _).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)
         change fderiv ℝ (g (i+j)) x _=_; rw[hh,fderiv_add (ht i) (ht j)]; rfl
       · apply (S).faithfully; funext x; obtain ⟨m,x,v,hx⟩:=x; rw[map_smul]; change (S).spectra _ _ _= c • ((S).spectra _ _ _); simp_rw [← (S).through (Hq).laws.toSymmetric (d:=d+1) _ v hx,show ∀ u, _= Points.gradient (n:=m+1) 0 a (yawn hK hf v ((S).representative d u)) x from fun u=> hp u m v x hx]
         let g(t:(S).Field d):= yawn hK hf v ((S).representative _ t); have hh:g (c • i)= c • g i:=funext fun z=> map_smul (((S).injectFront v z _).comp ((S).representative _)) c i
         have ht:DifferentiableAt ℝ (g i) x:= (((S).smooth_read (Hq).smooth _).contDiffAt ((conf_open _).mem_nhds hx)).differentiableAt (by simp)
         change fderiv ℝ (g _) x _=_; rw[hh,fderiv_const_smul ht]; rfl
end YM.Massive.Gust
#print axioms YM.Massive.Gust.bestow
