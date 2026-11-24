import YM.Vern.Vue
set_option maxHeartbeats 490000
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Lobo
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K}{φ:ℕ→ℕ}
variable (hf:Foil P K T)(H:K.Domestic)
variable (f:K.W≃ₗ[ℂ] K.W)
variable (v:K.W)
variable (h:∀ n:ℕ,∀ x:Points n, x∈conf n → ∀ y:Fin n→K.W,K.total n x (f ∘ y)= K.total n x y)
variable (V:Axis×Axis→K.W)(hV:Tarn.ChargeQ.Persona T V)(J:Axle K (fun a b=> V (a,b)))(g:Ortho.Skew)(hx:∀ i,f (V i)= V i)
include hf hV hx h
set_option quotPrecheck false
local notation "Jt"=> (fun a b=>V (a,b))
lemma halo : f (J.jet g v)= J.jet g (f v):=by
     apply detected hf; intro n p x he; let q:= f.symm ∘ p; have hq:f ∘ q=p:=funext fun i=>f.apply_symm_apply _; obtain ⟨χ,hχ⟩:=Work.A01.exists_window x he; rw[← J.relation g (f v) n x χ he hχ p,heads,← hq,←Fin.comp_cons,h (n+1) x he,←heads, ← J.relation g v n x χ he hχ q,←Fin.comp_cons]; unfold about fluxG; congr 1; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_ ; dsimp only; by_cases he':D (basis i) χ y=0; · simp [termG,he']
     unfold termG; refine congr_arg _ ?_; let z:=Points.cons y x; have hx':z∈conf _:= Work.A01.separated_of_D he hχ he'; have hu:= h (n+2) z hx' (Fin.cons (V (i,j)) (Fin.cons v q)); rw[Fin.comp_cons,hx] at hu; exact hu.symm
omit hx hV
include H
lemma inward(b:Axis): f (K.arc b v)= K.arc b (f v):=by
     apply detected hf; intro n p x he; let q:= f.symm ∘ p; have hq:f∘ q=p:=funext fun i=>f.apply_symm_apply _
     let Q(i: K.W)(p:Fin n→K.W)(x:Points (n+1)):= K.total _ x (Fin.cons i p); have ht: Q v q=ᶠ[𝓝 x] Q (f v) p:= ((conf_open _).eventually_mem he).mono fun i hi=>by unfold Q; rw[←hq,← Fin.comp_cons]; exact (h _ _ hi _).symm
     rw [heads,←hq,←Fin.comp_cons,h _ x he,heads,hq]; have hh(w:K.W)(p:Fin n→K.W): K.total _ x (Fin.cons (K.arc b w) p)=Analysis.D (Points.direction 0 b) (Q w p) x:=by unfold Q; rw [H.derivatives _ _ he, Fin.cons_zero, Fin.update_cons_zero]
     rw[hh,hh]; exact congr_arg (fun l:Points (n+1)→L[ℝ]ℂ=>l (Points.direction 0 b)) ht.fderiv_eq
omit h
-- spin arc. ∂_b along y of orientations. K.
variable (a:Axis)(w:Signed)(p:EuPin)(hw:p.Lifts w)
include hw
open Work.A01
lemma shift_b (x:E4): Ortho.move p.coord x= Ortho.move w.ortho x:=by rw [show p.coord=w.ortho from hw]
lemma axis_b : Ortho.move p.coord (basis a)= (signT w a) • basis (w.perm a):=by rw [shift_b hf H _ _ hw]; exact StressFlux.signed_basis w a
local instance choir_n (n:ℕ):ContinuousSMul ℝ (Points n):= inferInstance
set_option maxHeartbeats 4000000 in
lemma pith : T.spin p (K.arc a v)= (↑(signT w a):ℂ) • K.arc (w.perm a) (T.spin p v):=by
     apply detected hf; intro n q x hx; let F:= T.spin p; let y:= Points.move p.coord⁻¹ x; have hy:y∈conf _:=Points.move_in _ hx; let s:= F.symm∘q; let U:= Ortho.motion p.coord
     have hg: x=Points.move p.coord y:=by ext1 i; simp [y]; -- enough
     have hz:F∘s=q:=funext fun i=> F.apply_symm_apply _
     let M:Points (n+1)→ₗ[ℝ] Points (n+1):={ toFun:=Points.move p.coord,map_add':=fun i j=> by apply PiLp.ext; intro k; exact map_add U (i k) (j k),map_smul':=fun a i=>by apply PiLp.ext; intro k; exact map_smul U a (i k) }; let V:= M.toContinuousLinearMap
     have hi(w':K.W) : headG q x (F w')= headG s y w':=by rw[heads,heads, hg, ← hz, ←Fin.comp_cons]; exact hf.discrete (n+1) y hy p w hw _
     rw [show _= _ from hi (K.arc a v), map_smul]; let G(w:K.W)(q:Fin n→K.W)(x:Points (n+1)):= K.total _ x (Fin.cons w q); have h(x):headG q x (F v)=G (F v) q x:=heads ..
     have he(w:K.W)(q:Fin n→K.W)(u:Points (n+1))(hu:u∈conf _)(b:Axis):fderiv ℝ (G w q) u (Points.direction (0:Fin (n+1)) b)=headG q u (K.arc b w):=by change D _ (fun x=> _) _=_; rw [H.derivatives _ _ hu,Fin.cons_zero,Fin.update_cons_zero,heads]
     have hA: G (F v) q∘ V=ᶠ[𝓝 y] G v s:= ((conf_open _).eventually_mem hy).mono fun z he=> by
          have h:=hf.discrete (n+1) z he p w hw (Fin.cons v s); rw [Fin.comp_cons,hz] at h; exact h
     have hQ:V (Points.direction (0:Fin (n+1)) a) = (signT w a) • (Points.direction 0 (w.perm a)):=by
          apply PiLp.ext; intro j; by_cases hj: j=0; · subst j; change Ortho.move _ ((Points.direction (0:Fin (n+1)) a) _) =_; simp only [PiLp.smul_apply,Points.direction,points_apply, if_true, ↓reduceIte]; exact axis_b hf H _ _ _ hw
          change U _= _; simp [Points.direction,hj,Ne.symm hj]
     rw[← he v s y hy a,← hA.fderiv_eq,fderiv_comp, V.fderiv, ContinuousLinearMap.comp_apply,hQ,map_smul,(he _ q _ (show V y∈conf _ from (show V y=x from hg.symm).symm ▸ hx) _),show V y=x from hg.symm]; · rfl
     · exact ((H.smooth _ (Fin.cons (F v) q)).differentiableOn (by simp)).differentiableAt ((conf_open _).mem_nhds (show V y∈conf _ from (show V y=x from hg.symm).symm ▸ hx))
     exact V.differentiableAt
end YM.Vern
#print axioms YM.Vern.pith
#print axioms YM.Vern.inward
#print axioms YM.Vern.halo
