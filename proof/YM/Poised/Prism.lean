import YM.Poised.Project
import YM.Massive.Lining.Cameo
/-!
# color weights and actual label projection

Check color globally in all terms and cutoff, not projection on an artificial local support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus
variable {c : Side} {d : ℕ}
namespace Display
open TensorProduct
local notation "G" => SpinPol d
local notation "N" => Pairs (SpinMode d)
def linkOut (i:Finset N) : Pol d→ₗ[ℂ]GPol:= (TensorProduct.rid ℂ GPol).toLinearMap.comp (TensorProduct.map LinearMap.id (coef i))
lemma apart(i:Finset N)(x:GPol)(y:G) : linkOut i (x⊗ₜ[ℂ] y)=coef i y • x:=by unfold linkOut; rw [LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.id_coe,LinearEquiv.coe_coe,TensorProduct.rid_tmul]; rfl
lemma again(x:Pol d): ∑ i:Finset N,linkOut i x⊗ₜ[ℂ]mono i=x:=by
   induction x using TensorProduct.induction_on with
   | zero=> simp
   | tmul p q=> simp_rw [apart,smul_tmul, ←tmul_sum]; rw [write] -- smul_tmul might left & rew others
   | add p q hp hq=>simp_rw [map_add,add_tmul,sum_add_distrib,hp,hq]
lemma expected (x:Pol d)(i:Finset N)(J:Labels.Jet su): coef i (ready d J x)= Labels.read J (linkOut i x):=by
   induction x using TensorProduct.induction_on with
   | zero=> simp
   | tmul p q=> rw [apart,ready_t, map_smul,map_smul]; exact mul_comm ..
   | add p q hp hq=> simp_rw [map_add,hp,hq]
lemma distinct (x y:Pol d) (h:∀ J:Labels.Jet su,ready d J x=ready d J y): x=y:=by
   trans ∑ i,linkOut i x⊗ₜ[ℂ] mono i; exact (again x).symm
   refine Eq.trans ?_ (again y)
   exact Finset.sum_congr rfl fun i _=> congr_arg (fun u:GPol=>u⊗ₜ[ℂ]mono i) (Labels.eval_ext _ _ fun J=>by rw [← expected,h,expected])
lemma geom_unique (x y:Pol d)(k:ℕ)(h:∀ J:Labels.Jet su, iteratedDeriv k (fun t=>observation d J t x) 0=iteratedDeriv k (fun t=>observation d J t y) 0) : geometry k x=geometry k y:=by
   simp_rw [order_test] at h; exact distinct _ _ fun J=> smul_right_injective G (show (k.factorial:ℂ)≠0 from by exact_mod_cast k.factorial_ne_zero) (h J)
lemma unique (x y:Pol d)(hx:x∈cap d)(hy:y∈cap d)(h:∀ J:Labels.Jet su, Agrees (desired x J) (desired y J)): x=y:=by
   have hm i (hi:i≤d) : geometry i x = geometry i y:=geom_unique x y i fun J=>by simp_rw [observe]; exact (h J).2.2 i hi
   calc x = drips d x := (drips_identity x hx).symm
        _ = drips d y:=by unfold drips; rw [LinearMap.sum_apply,LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i hi=> hm i (by simpa using hi)
        _ = y:=drips_identity y hy
lemma clm_step {E Z : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup Z][NormedSpace ℝ Z](f:ℝ→E)(k:ℕ)(x:ℝ)(hf:ContDiffAt ℝ k f x)(L:E→L[ℝ]Z): iteratedDeriv k (L ∘ f) x=L (iteratedDeriv k f x):=by unfold iteratedDeriv; rw [L.iteratedFDeriv_comp_left hf (le_refl _)]; rfl
variable (d)
abbrev luminous (u:su.El) : SpinPol d→ₐ[ℂ]SpinPol d:= adapter (colorTable u) (star (colorTable u)).transpose
variable (u:su.El) {d}
lemma visual (J:Labels.Jet su)(x:Pol d) : ready d J (colorAct u x)= luminous d u (ready d (Labels.colored u J) x):=by
   induction x using TensorProduct.induction_on with
   | zero=>simp
   | tmul p q=> rw [colorAct,TensorProduct.map_tmul,ready_t,ready_t,map_smul]; change Labels.read J (Labels.changed (fun _=>Labels.Taylor.paint u) p) • luminous d u q = _; rw [Labels.eval_changed]; rfl -- abbrev didn't display
   | add x y hx hy=> simp_rw [map_add,hx,hy]
private lemma scales_eye (v:ℝ): scaled (d:=d) v*colorTable u=colorTable u*scaled v:= by
   ext i j; unfold scaled; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; unfold colorTable; simp only [Matrix.of_apply]; split_ifs with h; swap; · rw [mul_zero,zero_mul]
   rw [h.2,mul_comm]
lemma commuting (y:G)(v:ℝ) : endor v (luminous d u y) = luminous d u (endor v y):=by
   unfold endor luminous; rw [adapt_together,adapt_together, ← mono_color u, scales_eye,scales_eye] -- arg
lemma lamp_obs (t:ℝ)(x:Pol d)(J:Labels.Jet su) : observation d J t (colorAct u x)=luminous d u (observation d (Labels.colored u J) t x):=by
   change endor t (ready d (scaleJet J (t^2)) (colorAct u x)) = luminous d u (endor t _); rw [visual,commuting,show Labels.colored u (scaleJet J (t^2))=scaleJet (Labels.colored u J) (t^2) from funext fun i=>map_smul (Labels.Taylor.paint u) _ (J i)] -- map_smul with smul cast
lemma luminousG (x:Pol d)(k:ℕ): colorAct u (geometry k x)= geometry k (colorAct u x):=by
   apply Display.distinct; intro J; rw [visual]; let p:= (luminous d u); let L':=(p.toLinearMap.restrictScalars ℝ).toContinuousLinearMap; apply smul_right_injective G (show (k.factorial:ℂ)≠0 by exact_mod_cast k.factorial_ne_zero); dsimp only; rw [← order_test]
   change (k.factorial:ℂ) • luminous d u _= _; rw [← map_smul, ← order_test]; symm; simp_rw [lamp_obs]; exact clm_step _ k 0 (painted _ _ _).contDiffAt L'
lemma radiant_cap{x:Pol d}(h:x∈cap d): colorAct u x∈cap d:=by
   have he: colorAct u x=drips d (colorAct u x):=calc
      _=colorAct u (drips d x):=by rw [drips_identity _ h]
      _=_:=by simp_rw [drips,LinearMap.sum_apply,map_sum,luminousG]
   rw [he]; exact drips_in (colorAct u x)
end Display
namespace Beacon
open TensorProduct Display Lining
variable (H:TaperHol)(b : Cover)
local notation "F" => Lat.Fields c 6
local notation "G" => SpinPol d
local notation "N" => Pairs (SpinMode d)
variable (u:su.El)
lemma glitter (d:ℕ)(n:Side)(e:Edge Cover)(x:ℝ)(J:Labels.Jet su) : H.flow n d (Labels.colored u J) x e=fun t=> u* H.flow n d J x e t * u⁻¹:=by
   apply (H.solves ..).unique; have ht:= Work.G01.solves_adjoint u (H.solves n d J x e); convert ht using 1; funext s; simp only [Taper.connection,Source.partConnection,Source.potential,Labels.colored,Labels.Taylor.paint_value,map_smul, map_sum]
lemma jointGlow (d:ℕ)(n:Side)(x:ℝ)(J:Labels.Jet su): current (c:=n) H b d (Labels.colored u J) x = Lattice.gauge (fun _=>u) (current H b d J x):=by
   funext i; unfold current views Lattice.gauge spark; simp_rw [← focused,glitter] -- gauge args ok
private lemma warL (t:ℝ): glow (c:=c) (d:=d) H.T b t=nacre (fun x y=> (spun H.T b x*profile y (offset b x) t) • 1):=by ext i j; rw [imprints]; simp only [YM.Massive.Poised.Beacon.glow,Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,smul_eq_mul]; by_cases ht:i.2=j.2 <;> by_cases hh:i.1.2=j.1.2 <;> simp [ht,hh]
lemma spherical (t:ℝ) : Lat.rotates 6 (fun (_:Site c)=>u)*glow (d:=d) H.T b t=glow (d:=d) H.T b t*colorTable u:=by
    rw [Ferry.sight,eye_color,warL,spar_mul]; change _=nacre _ * spar (⇑(Equiv.refl _)) _; rw [spar_after]; congr 1; funext i j; simp
lemma antique (t:ℝ) : (star (Lat.rotates 6 (fun (_:Site c)=>u))).transpose*glow (d:=d) H.T b t=glow (d:=d) H.T b t*(star (colorTable u)).transpose:=by
   rw [Ferry.sight,eye_color, ← mstar_sq, ← mstar_sq,spar_color,spar_color,warL,spar_mul]; change _=nacre _ * spar (⇑(Equiv.refl _)) _; rw [spar_after]; congr 1; funext i j; simp
lemma observed (J:Labels.Jet su)(x: Grid c→F)(t:ℝ) : moment (d:=d) H b J (fun V=> slots 6 (fun _=>u) (x (Lattice.gauge (fun _=>u) V))) t = luminous d u (moment (d:=d) H b (Labels.colored u J) x t):=by
   rw [moment,moment,jointGlow]; unfold slots luminous; rw [adapt_together,adapt_together,spherical,antique]
lemma coloredO (x:Grid c→F)(p:Pol d)(h: ActionTest H b x p) : ActionTest H b (fun V=> slots 6 (fun _=>u) (x (Lattice.gauge (fun _=>u) V))) (colorAct u p):=by
   intro J; rw [← funext (observe J (colorAct u p))]; simp_rw [lamp_obs]; rw [funext (observed H b u J x)]; let L':=((luminous d u).toLinearMap.restrictScalars ℝ).toContinuousLinearMap; have ht:=h (Labels.colored u J); rw [← funext (observe _ p)] at ht
   refine ⟨L'.contDiff.contDiffAt.comp _ ht.1,L'.contDiff.contDiffAt.comp _ ht.2.1,fun i hi=>?_⟩
   change iteratedDeriv i (L' ∘ moment H b (Labels.colored u J) x) 0=iteratedDeriv i (L' ∘ fun h=>observation d (Labels.colored u J) h p) 0; rw [clm_step _ _ _ (ht.1.of_le ?_), clm_step _ _ _ (ht.2.1.of_le ?_), ht.2.2 i hi] <;> exact_mod_cast hi
lemma chooses {x:Grid c→F}{v w:Pol d}(hv : v∈cap d)(hw:w∈cap d)(h:ActionTest H b x v)(h':ActionTest H b x w): v=w:= Display.unique v w hv hw fun J=> ⟨(h J).2.1,(h' J).2.1,fun k hk=> ((h J).2.2 _ hk).symm.trans ((h' J).2.2 k hk)⟩
theorem obtainsL (x: Grid c→F) (hx: ContDiffAt ℝ (d:WithTop ℕ∞) (x∘increment 1) 0) (he:∀ u:su.El,(fun V=> slots 6 (fun _=>u) (x (Lattice.gauge (fun _=>u) V)))=x) : ∃! p:Label d, ActionTest H b x p.val:=by
    obtain ⟨v,hv,ht⟩:= obtainsD H b x hx; have hh (u:su.El): colorAct u v=v:= chooses H b (radiant_cap u hv) hv (he u ▸ coloredO H b u x v ht) ht
    exact ⟨⟨v,(label_law _).2 ⟨hv,hh⟩⟩,ht,fun y hy=>Subtype.ext (chooses H b ((label_law y.val).1 y.property).1 hv hy ht)⟩
end Beacon
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Beacon.obtainsL
