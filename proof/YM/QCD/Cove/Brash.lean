import YM.QCD.Cove.Quid
/-! # Finite-inventory pricing. Geometric incidence all hinges on hats, including negative flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Cove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Send Fj Filter
open Further.ShellBirth49.Fusing Collide
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f: Side} {E D J:Type}{F:ℕ}{S:Ratio c f} {h h' a q t:ℝ}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "I"=> Fj D E J
local notation "R"=> Junta c f F

lemma limits_card (X:Support f): (limits (F:=F) X).card=2*X.card * Fintype.card Fiber * F:=by
  let Y := ((X ×ˢ (univ:Finset Fiber)) ×ˢ (univ:Finset (Flavor F)))
  have he: limits (F:=F) X= Y.disjSum Y:=by ext i; rcases i with ⟨⟨x,z⟩,f⟩|⟨⟨x,z⟩,f⟩ <;> simp [limits,Y,locationP]
  rw [he]; dsimp only [Y]; simp only [card_disjSum,card_product,card_univ]; unfold Flavor; simp; ring

lemma full_tip {X:Water c f F} (hp:0<h')(i:Keys f F)(p:ℝ)(hh:h'*(∑ j,‖X i j‖) ≤ p): load (fun _=>h') (wipe A B X (atom (ha _ _ _ i)))≤p:=by
  rw [show ha c f F i=head A B i from rfl,wiper]; apply (load_sum ..).trans
  exact le_trans (le_of_eq (by rw [mul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [load_scale,load_atom _ (fun _=>hp) j]; exact mul_comm ..)) hh
variable (G:Send S F D) (P:Rise f F E J)

structure Peak (t h h' q:ℝ)(μ:D→ℝ) : Prop where
 bud :0<h
 cup :0<h'
 post :1≤q
 spare (i:D)(U):Ledge.Pledge (rateF c f F h h') (bucks G i U) (μ i)
 earn (i:Keys f F)(U): Healthy t (halo (G.trim+1) {locationP i}) U → h'*(∑ j,‖G.shortP U i j‖) ≤ h
 held (i:Keys f F)(U): h'*(∑ j,‖G.shortP U i j‖)≤q*h
abbrev invSize (s: Finset I) := ∑ i∈spent s, (P.front i).inv.card
def kappa (r F:ℕ):ℕ:=2*(r+r+1)^4*Fintype.card Fiber*F


-- assume input budgets uniform from shape. Need P.spends?
structure Cents (β:E→ℝ)(κ:J→ℝ) (h t:ℝ):Prop where
 pos : ∀ i, 0 ≤ β i
 non : ∀ i, 0 ≤κ i
 cost i U : load (fun _=>h) (light _ (P.reading t U i)) ≤ β i
 funds i U : load (fun _=>h) (light _ (P.plug i U))≤κ i

variable {μ:D→ℝ}{β:E→ℝ}{κ:J→ℝ}
lemma k_payment (s:Finset I):
    let T := (limits (halo (G.trim+1) (P.wish (spent s)))).map (ha c f F)
    T.card ≤ kappa (G.trim+1) F*invSize P s:=by
     intro T; let Z:= halo (G.trim+1) (P.wish (spent s))
     unfold T; rw [card_map,limits_card]; unfold kappa; have hm: Z.card ≤ invSize P s*((G.trim+1)+(G.trim+1)+1)^4:= (Corona.halo_size ..).trans (Nat.mul_le_mul_right _ (Finset.card_biUnion_le ..)); change (2*Z.card*_)*_ ≤ _; refine le_trans (Nat.mul_le_mul_right F (Nat.mul_le_mul_right (Fintype.card Fiber) (Nat.mul_le_mul_left 2 hm))) ?_ ; exact le_of_eq (by ring)
lemma per_bill (M: Peak G t h h' q μ)(s: Finset I)(U:Grid f)(hv:closeS G P t s U):
    let Z := halo (G.trim+1) (P.wish (spent s)); let T:Finset R := (limits Z).map (ha _ _ _); let Y:=rateF c f F h h'; let V i:=if i∈T then q*Y i else Y i
    ∀ i:R,i∈hooks S (coreW G P s)→load (fun _=>h') (wipe A B (G.shortP U) (atom i)) ≤ V i :=by
      intro Z T Y V i h
      rcases splits_index i with ⟨i,rfl⟩|⟨i,rfl⟩
      · change _ ≤ V (ha c f F i); unfold V; split
        · rw [show Y _ = _ from wagesA B i _ _]; exact full_tip M.cup i _ (M.held _ _)
        next hj=>
         rw [show Y _ = _ from wagesA B i _ _]; apply full_tip M.cup; apply M.earn
         apply Finset.disjoint_left.mpr; intro j hk hi
         change ha c f F i∈_ at h; rw [hooked,rootA] at h
         have he : j∈P.wish (spent s) := by rw [show P.wish _ = _ from hv]; refine mem_inter.mpr ⟨hi,?_⟩; rw [brim_eq]; exact Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr h) hk
         have hhi : i∈ limits Z := mem_filter.mpr ⟨mem_univ _,by
           obtain ⟨l,hl,hx⟩:= halo_spec.mp hk; rw [mem_singleton.mp hl] at hx; exact halo_spec.mpr ⟨j,he,(separation_comm ..).trans_le hx⟩⟩
         exact hj (Finset.mem_map_of_mem _ hhi)
      · rw [tails,load_atom _ (fun _=>M.cup)]; unfold V; simp only [Y,rateF,wagesB]; split; exact le_mul_of_one_le_left M.cup.le M.post; exact le_rfl
lemma cruises (M: Peak G t h h' q μ)(s:Finset I)(U:Grid f)(ht:P.Wave t)(hv:closeS G P t s U)(hz:Cents P β κ h t):
   load (fun _=>h') (light _ (dye G P t s U)) ≤ q^(kappa (G.trim+1) F * invSize P s)*priceSet s μ β κ:=by
   let X := light _ (crate G P t s U); let Z:= halo (G.trim+1) (P.wish (spent s)); let T : Finset R := (limits Z).map (ha _ _ _)
   have hc:T.card ≤ kappa (G.trim+1) F*invSize P s:= k_payment G P s
   let Y:=rateF c f F h h'; let V i:= if i∈T then q*Y i else Y i; have he i : 0< Y i := by cases i with
      | inl i=> cases i <;> first| exact M.bud| exact M.cup
      | inr i=> cases i <;> first| exact M.bud| exact M.cup
   have hw i:0< V i:= by unfold V; split; exact mul_pos (zero_lt_one.trans_le M.post) (he _); exact he _
   have hp (i:R) (h:i∈hooks S (coreW G P s)):load (fun _=>h') (wipe A B (G.shortP U) (atom i))≤ V i:=per_bill G P M s U hv i h
   rw [show light (Keys c F) (dye G P t s U) = wipe A B (G.shortP U) X from rfl]
   refine le_trans (ferry (wipe A B (G.shortP U)) hw hp X (framed G P t s U ht)) ?_
   refine (sail T Y q he M.post X).trans ?_
   have hx:load Y X ≤ priceSet s μ β κ:= makes G P _ _ _ M.bud s U (fun i _=> M.spare i _) (fun i _=> hz.cost i _) (fun i _=> hz.funds i _)
   exact mul_le_mul (pow_le_pow_right₀ M.post hc) hx (load_nn ..) (pow_nonneg (zero_le_one.trans M.post) _)
lemma summing (M:Peak G t h h' q μ)(s:Finset I)(U:Grid f)(ht:P.Wave t)(hz:Cents P β κ h t):load (fun _=>h') (light _ (hue G P t s U))≤ q^(kappa (G.trim+1) F * invSize P s)*priceSet s μ β κ:=by
  unfold hue; split
  next hi=>exact cruises G P M s U ht hi.2 hz
  next=> rw [map_zero,load_zero]; exact mul_nonneg (pow_nonneg (zero_le_one.trans M.post) _) ((load_nn ..).trans (makes G P _ β κ M.bud s U (fun i _=> M.spare i _) (fun i _=>hz.cost i _) (fun i _=> hz.funds i _)))
end YM.QCD.Cove
