import YM.Dart.Bier
/-!
  A discrete telescoping measurement of one-slot derivative budget. Does not
  pay powers of lattice size and doesn't extrapolate through interpolation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) (d:ℕ)
local notation "S"=> C.S
set_option quotPrecheck false
variable {P d} {E:Hub.Invest P d}(H:Rack E)
namespace GaugeP
variable {Z: Laurel d}{J: Landing P.sym Z}(K:GaugeP P Z J){β ν:ℝ}(hp:C.Path β ν)(hS:Sway C.S)(G:Capital P d 1)
variable {H}(x:(i:ℕ)→stalk C i){P₀:ℕ→ Label d}
-- choose genuine fine support interior.
variable (b:Axis)
-- Public API for insertion sequences. Convergence along point shadows.Shifts budgets.
include hp hS G
lemma attentive (h:∀ᶠ j in atTop,∃ V:ℝ, 0≤V∧∀ᶠ i in atTop, GreenP C i j (x i) V):∃ V:ℝ,0 ≤ V∧ ∀ᶠ i:ℕ in atTop,∃ O:Merit K i, ‖O.testR (x i)‖≤V:=by
     obtain ⟨j,⟨V,hV,hG⟩,G,hG',he⟩:= (h.and (K.valves hp hS G)).exists
     refine ⟨_,mul_nonneg hG' hV,?_⟩; filter_upwards [K.lively hp,he,hG] with i hi hp hu; obtain ⟨p,hh⟩:=hi; exact ⟨Merit.solo hh, (congr_arg Norm.norm (Merit.onlyX hh _)).trans_le (hp _ hh _ V hV hu)⟩ -- name Dot
-- committed coefficients from general ARC.And decay test budgets erosion via deterministic allocations.
structure Brush (E:Hub.Invest P d)(K:GaugeP P Z J) (x:(i:ℕ)→stalk C i)(a:ℕ→ Stokes d→ℂ):Prop where
    cost : ∃ C:ℝ,0 ≤ C∧∀ᶠ i in atTop,‖a i‖ ≤ C
    dimin (n:ℕ)(p:Fin n) : ∀ᶠ j in atTop,∀ (U:(i:Fin n)→ (k:ℕ)→stalk C k)(u:Fin n→ℝ),(∀ᶠ i in atTop,∀ k,k≠p→ GreenP C i j (U k i) (u k))→∀ ε:ℝ,0<ε →∀ᶠ i in atTop,∀ b:Fin n→ Cover, seaM C i j b → ‖readS C i (update (fun k=> U k i) p (x i - stem P d i (K.ridge i (a i)))) b‖ ≤ ε
-- helper decomposition of readS etc
omit hp hS G
noncomputable def readZ(i:ℕ)(p:Fin d)(x:Fin d→ Cover)(u:Fin d→stalk C i): stalk C i→ₗ[ℂ]ℂ where
    toFun X:= readS C i (update u p X) x
    map_add' X Y:=by
         let G(j:Fin d):= u j (x j); let V:=MultilinearMap.mkPiAlgebraFin ℂ d (Insertion (C.S.side (C.R i) (C.N i)) 6)
         have h(Z:stalk C i): (fun j=> update u p Z j (x j))= update G p (Z (x p)):=by ext1 j; by_cases h:j=p; subst j; simp; rw [update_of_ne h,update_of_ne h]
         have hh(U':Fin d→stalk C i):readS C i U' x=((C.A i).regulator).average (List.ofFn (fun j=> U' j (x j))).prod:=rfl; rw [hh,hh,hh,h,h,h,←map_add]; exact congr_arg _ (V.map_update_add ..)
    map_smul' z X:=by
         let G(j:Fin d):= u j (x j); let V:=MultilinearMap.mkPiAlgebraFin ℂ d (Insertion (C.S.side (C.R i) (C.N i)) 6)
         have h(Z:stalk C i): (fun j=> update u p Z j (x j))= update G p (Z (x p)):=by ext1 j; by_cases h:j=p; subst j; simp; rw [update_of_ne h,update_of_ne h]
         have hh(U':Fin d→stalk C i):readS C i U' x=((C.A i).regulator).average (List.ofFn (fun j=> U' j (x j))).prod:=rfl; rw [hh,hh,h,h, ←map_smul]; exact congr_arg _ (V.map_update_smul ..) -- class
include hS hp G
lemma jewel {a:ℕ→Label d}(h:Arc H x a) {V:ℝ}(hv:∀ᶠ i in atTop, ‖K.tip E i (a i)‖ ≤ V ∧ ‖K.tipEnd E i (a i)‖ ≤ V*E.scale i)(hx:0 ≤V):Brush E K x (fun i=> K.tip E i (a i)):=by
    refine ⟨⟨V,hx,hv.mono (fun _ hi=>hi.1)⟩,fun n p=>?_⟩; filter_upwards [(tendsto_add_atTop_nat 1).eventually h.tideP, Investment.creditW E,hS.high.eventually_gt_atTop (8*n)] with j hJ hj hu
    obtain ⟨F,hF,f⟩:=hJ; obtain ⟨Gm,hG,K'⟩:=hj; intro U u h ε he; let A:= ∏ i∈ Finset.univ.erase p,u i; let Xa i:= F i*A+((V*(E.scale i* Gm i))*A);
    have ht:Tendsto Xa atTop (𝓝 0):=by simpa only [Xa,mul_zero,zero_mul,zero_add] using (hF.mul_const A).add (((hG.const_mul V)).mul_const A)
    let Wi(i:ℕ):= V*(E.scale i*Gm i)
    filter_upwards [h,hv, K.slices hp hS G E,K',f,hp.uv.tendsto_atTop.eventually_ge_atTop (j+1),ht.eventually_le_const he] with i h hx' hJ hK hF hm hΩ b hb
    let L:= readZ (C:=C) i p b (fun k=> U k i); let q:= K.tip E i (a i); let Q:= K.tipEnd E i (a i); let f:= stem P d i; let T:= x i-f (a i); let Z:= f (Investment.face E i Q); have hP: x i - f (K.ridge i q) = T + Z:=by
        have he:= congr_arg (fun a:Label d=> f a) (hJ (a i)); simp only [map_add] at he; change f (K.ridge i q)+Z=f (a i) at he; unfold T; rw[←he]; abel
    have hk(X:ℝ): ∏ k:Fin n, update u p X k=X*A:= by let v:=update u p X; have h:∏ k∈Finset.univ.erase p,v k=A:= Finset.prod_congr rfl fun k hk=> update_of_ne (Finset.ne_of_mem_erase hk) ..; rw[show ∏ k,v k= v p*∏ k∈ Finset.univ.erase p,v k from (mul_prod_erase _ _ (mem_univ p)).symm,h]; simp only[v,update_self]
    have h₀ : ‖L T‖ ≤ F i * A:=by
         let f:=update (fun k=> U k i) p T; have hg:n*8<(C.S.step j).L.val:= (mul_comm n 8).trans_lt hu;
         exact (oneK hp i j p f (update u p (F i)) (fun k hh=> by unfold f; rw [update_of_ne hh,update_of_ne hh]; exact h k hh) (by unfold f; rw [update_self,update_self]; exact hF.2) b hb hg hm).trans_eq (hk _)
    have h₁ : ‖L Z‖ ≤ Wi i * A:=by
         let f:= update (fun k=> U k i) p Z; have hg:6*n<(C.S.step j).L.val:=lt_of_le_of_lt (Nat.mul_le_mul_right _ (by norm_num)) hu
         let v:= update u p (Wi i); have hy(k:Fin n): GreenP C i j (f k) (v k):=by
              by_cases hh:k=p; · rw[hh]; unfold f v; rw [update_self,update_self]; exact GreenP.mono (hK.2 Q) ((mul_le_mul_of_nonneg_right hx'.2 hK.1).trans_eq (mul_assoc ..))
              unfold f v; rw [update_of_ne hh,update_of_ne hh]; exact h k hh
         exact (reapS i j f v hp hy b hb hg hm).trans_eq (hk _)
    change ‖L (x i-f (K.ridge i q))‖ ≤ _; rw[hP,map_add]; apply (norm_add_le ..).trans; exact (add_le_add h₀ h₁).trans hΩ
lemma braidVal (h:Arc H x P₀)(hq:∀ᶠ j in atTop,∃ V:ℝ,0 ≤ V∧∀ᶠ i in atTop, GreenP C i j (x i) V): Brush E K x (fun i=> K.tip E i (P₀ i)):=by
     obtain ⟨B,hB,H⟩:=K.attentive hp hS G x hq; obtain ⟨V,W,hV,hW,hP⟩:= twain K hp hS G h B hB H -- dot issue sig
     apply jewel K hp hS G x h (hP.mono (fun i hi=> ⟨hi.1.trans (le_add_of_nonneg_right hW),hi.2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hV) (E.pos i))⟩)) (add_nonneg hV hW)
lemma braidDer (h:Arc H (fun i=>lDer C i b (x i)) P₀)(hq:∀ᶠ j in atTop,∃ V:ℝ,0 ≤ V ∧∀ᶠ i in atTop, GreenP C i j (x i) V):Brush E K (fun i=> lDer C i b (x i)) (fun i=>K.tip E i (P₀ i)):=by
     obtain ⟨B,hB,H⟩:=K.buyDer hp hS G b x hq; obtain ⟨V,W,hV,hW,hP⟩:= twain K hp hS G h B hB H
     apply jewel K hp hS G _ h (hP.mono (fun i hi=> ⟨hi.1.trans (le_add_of_nonneg_right hW),hi.2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hV) (E.pos i))⟩)) (add_nonneg hV hW)
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.braidDer
