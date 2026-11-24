import YM.Play.Dells
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace YM.MassiveQCD.Play
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {ι κ I E J D:Type}{N:ℕ}
variable {δ b:ℝ} (H:Cash W τ μ L Q o C T (trimP T O δ β b)){P₀:Rise f N E J}
variable (G:Send S.ratio N D) (M:Fj D E J→Support c)
variable [Fintype I]
variable (X:Stitch.Tablet P₀ I)(z:I→Site f)(a:ℝ)
local notation "t"=>O.threshold
local notation "M'"=> Ribbon.ample N I
local notation "z'"=> S.ratio.parent ∘ z
local notation "I'"=> Ribbon.Spine I
open Stitch
local notation "Β"=>banknote N z' a
variable (Y:Fleet H κ (ample N I))
local notation "Ξ"=> closet H G M X z a
local notation "Tx"=> united (Ξ) Y
variable {q':I→Bool}(hw:X.Wave O.threshold q' z)(hk:Cove.Count G P₀ M)
namespace Camp
open TabletV
variable (p: Finset (Fj D E J))
local notation "V'"=> Wound M
local notation "P'"=> Piece S (Wound M ⊕ κ)
local notation "p'"=> plume P₀ G M p
variable (χ:Chi)(U:Grid c)
open PhysicalNext.Repeat.Greenbelt
variable (hs : ∀ j∈ leftE p, (X.spine j).Nonempty) (he:spent p=∅)
set_option quotPrecheck false
local notation "H'"=> student H G M X z a Y p hk hw hs he
local notation "Zs"=> campus H G M X z a Y p hk hw hs he
local notation "Ip"=> ↥(plume P₀ G M p)
local notation "Cv"=> month (P₀:=P₀) M G p
local notation "sp" r=> prism T τ χ o.K U (allot r)
local notation "Sp" r=> planted (prism T τ χ o.K U (allot r)) (∅:Finset (Head S))
variable (hV:(united (closet H G M X z a) Y).Famous)
variable (Ω:Support c) (hM:M=roof G P₀ 30 (radiusB τ))
open Hypnos
variable (Z:Coat T F)(hZ:Z.manifest)(htZ:Z.x=τ)(hwZ:Z.width=o.K)
-- every interested trial (even D pin where separated) might need health on its FULL main support AND all its halos. 
local notation "Hz"=> (Cupola.withdraw N z' a)
structure Ration (u v:ℝ):Prop where
    receipt : ∃ g: Wound M→ℝ,Ac.Hit ((closet H G M X z a).ground) (radiusB τ) g u v ∧ ∀ i U V, ‖token c (ample N I) a ((closet H G M X z a).works i U V)‖ ≤ g i
-- estimate all
variable (h₀:owned G M p Ω) (w':Air f su)
variable {u v γ:ℝ} (hR:Ration H G M X z a u v)
private lemma gift (ha:1≤a) (x:Patio (Keys c N⊕Spine I)): ‖x‖≤ ‖token c (ample N I) a (Β x)‖:=by
   let f:Keys c N→ℝ:=fun _=>a; let q:I'→ℝ:=fun _=>1; let Q:= expRate (p:=f) (q:=q); have hh i:1 ≤ Q i:=by cases i with | inl=>exact ha| inr=>exact le_rfl
   refine (Stitch.Tablet.minimal _ _ hh x).trans_eq ?_
   rw [Loom.pulse,Cupola.withdrawCost N z' a (zero_lt_one.trans_le ha),fiscal (p:=f) (q:=q) (fun _=>zero_lt_one.trans_le ha) (fun _=>zero_lt_one)]; refine sum_congr rfl fun i _=> ?_; simp only [q,prod_const_one,one_mul]; rfl
include hw hk he hs
variable (Lp:Finset I)(hLp: ∀ i∈ leftE p,X.spine i⊆ Lp)
include hLp
lemma spendsV (u':V'→ℝ)(hQ:Ac.Hit ((Ξ).ground) (radiusB τ) u' u v)(h0:0≤u')(hu:0≤u): SumBudget (fun i:Ip=> u' (child G M p i)) (Lp.card*v):=by
   let y(i:I)(j:V'):= if (z') i∈ (Ξ).ground j then u' j * currency (radiusB τ) u ((Ξ).ground j) else 0
   have hp i (hi:i∈ Lp):SumBudget (y i) v:= hQ ((z') i)
   have hh:= budget_pull (child (P₀:=P₀) G M p) (childInj G M p) (budget_over Lp y (fun _=>v) hp)
   have hx : ∑ _i∈Lp,v = Lp.card*v:=by simp [nsmul_eq_mul]
   rw [hx] at hh; refine budget_mono hh (fun i=>h0 (child G M p i)) ?_
   intro i; let j:=child G M p i; have hs₀:=mem_powerset.mp (mem_filter.mp i.2).1; obtain ⟨b,hb⟩:= lush (P:=P₀) G i.val j.2.1 (spentP _ _ hs₀ he) (mem_filter.mp i.2).2.2; have ht:b∈leftE p:=mem_toLeft.mpr (mem_toRight.mpr (hs₀ (mem_toRight.mp (mem_toLeft.mp hb))))
   obtain ⟨k,hk'⟩:=hs b ht; refine le_trans ?_ (single_le_sum (f:=fun i=> y i j) (fun i hi=> (hp i hi).1 j) (hLp b ht hk'))
   unfold y; rw [if_pos]; exact le_mul_of_one_le_right (h0 _) (Real.one_le_exp (mul_nonneg hu (Nat.cast_nonneg _))); exact X.endowment G hw hk i.val (mem_image_of_mem _ (mem_union_left _ (mem_biUnion.mpr ⟨_,hb,hk'⟩)))
include hR
lemma burningB (ha:1≤a)(hu:0≤u): ‖Hz (skyM H G M X z a Y p F Z w')‖≤ Real.exp (Lp.card*v):=by
   obtain ⟨g,hg,hG⟩:= hR.receipt
   let P(i:Ip):= child G M p i; have hp:= spendsV H G M X z a hw hk p hs he Lp hLp g hg (fun i=> (norm_nonneg _).trans (hG i 1 1)) hu
   let W i:= (Tx).coming (Sum.inl (P i)) Z w'
   have hX(i:Ip): ‖Hz (W i)‖ ≤ g (P i):=by
       let b₁:= (Ξ).riseP Z w' (P i); let x:= Z.input (Z.liftA β w'); let y:= X.hue t G i.val x; let b:=δ⁻¹ ^ Loom.budget P₀ i.val
       have hW:W i=b₁ • b • Β y:=rfl
       have hs : ‖token c M' a (W i)‖ ≤ g (P i):=by
          have hb:b₁ ∈ Set.Icc 0 1:= Z.conserve ..; rw [hW,map_smul,norm_smul,Real.norm_of_nonneg hb.1]; exact (mul_le_of_le_one_left (norm_nonneg _) hb.2).trans (hG (P i) x Z.V)
       have h y (b:ℝ): Β (b • y) = b • Β y:=map_smul ((Β).toLinearMap.restrictScalars ℝ) ..
       rw [hW,←h,←h] at hs ⊢; rw [Cupola.home N z' a (zero_lt_one.trans_le ha)]; exact (gift (S:=S) z a ha _).trans hs -- H? gift depends S but not H include? signature.
   unfold skyM; rw [map_sum]; apply le_trans (norm_sum_le ..)
   refine le_trans ((sum_le_sum (g:=fun s:Finset Ip=> ∏ i∈s,g (P i)) (?_))) (budget_sum (Product.set_products hp) _); intro j _; unfold weald; rw [map_prod]; exact (Finset.norm_prod_le ..).trans (prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> hX i))
end Camp
end YM.MassiveQCD.Play
#print axioms YM.MassiveQCD.Play.Camp.burningB
