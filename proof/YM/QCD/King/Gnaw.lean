import YM.QCD.King.Rental
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R:BudgetPoint}
variable {H:Cash W τ μ L Q o C T (trimP T R δ β b)}{ι D E K:Type}{N:ℕ}
local notation "M"=> radiusB τ
local notation "t0"=> R.threshold
variable {j k l m n i:ℕ}{L': Flight j k}{d:f.val=c.val*L'.L.val}
variable {X:Run.St f} {W':ℕ→Atom su 2}{J:Plan k}{η ξ p p' z r R' v u:ℝ}
local notation "G"=> sliceL L' d
variable (H : Cash W τ μ L Q o C T (trimP T R δ β b)) (G₁:Swathe L' d X W' J u v η p p' n)
open Blaze Vine King Kings Jets.Touch
-- Honest direct state all. from Woods enforce higher (than price) for Cargo, Uniform χ. Tender.
local notation "π"=>VarnC H G₁ N
lemma iceM (h:S.ratio=G)(ht: RentP G₁ N M (fiery su τ S.patch.L) z R' (wear L τ))
  (M₁:ℕ)(A a:ℝ)(χ:Chi)(hW:∀ (F:Tree.Forest S.ratio)(Y:Coat T F), Y.x=τ → Y.width=o.K→Y.manifest →∀ i:Varn f c,waxV i=none→¬Shell.Inside (siteH i S.ratio) Y.seeds (18*M) →∀ w:Directions su f,Cargo Y (2*o.a) w (vap i S.ratio M) → load (fun _=>R') (Cove.light _ (sliceF G₁ N M i (Y.input w))) ≤ z):
   Honest (VarnC H G₁ N) A 0 (fan L (1/4) τ) (fun i=>Real.exp 1*Port.shells G₁ N M R' z i) R' a χ M₁ (fun i=>siteH i S.ratio) ((univ:Finset (Varn f c)).filter fun j=>waxV j=none) (18*M) (S.ratio.count.val^4+1):=by
    let m:=radiusB τ; let p i:= Real.exp 1*Port.shells G₁ N M R' z i; let E:=fan L (1/4) τ
    have hE:0<E:=fan_pos ..; have hx i:0≤p i:=mul_nonneg (Real.exp_pos _).le (by unfold Port.shells; split; exact ht.profit.le; exact Port.grew G₁ _ ht.growth ht.toll)
    refine ⟨hx,le_rfl,hE.le,fun F U he hh hz hS T _ _ _ x V Z hu hy i H₀=> ?_,counters _⟩
    intro K; let w:=worldZ U β Z; let q := broke G₁ N M i (U.input w)
    have hC: King.windy (VarnC H G₁ N) 0 i=0:= zero_mul _
    have hs (A:ℝ) (hp:‖token c N R' q‖ ≤ A): Brush M₁ A (King.windy (VarnC H G₁ N) 0 i) K x:=(Brush.certified (show 0 ≤ King.windy _ 0 i from hC.ge) (wearK c N R' q)).climb hp le_rfl
    have ht' := mountains G₁ ht (U.input w) i
    have hr: ¬ (zoneG (L:=L') (H:=d) (B:=fiery su τ S.patch.L) (U.input w) i M) → Brush M₁ (p i) (King.windy (VarnC H G₁ N) 0 i) K x:= by intro hm; rw [if_neg hm] at ht'; exact hs _ ht'
    by_cases hQ: zoneG (L:=L') (H:=d) (B:=fiery su τ S.patch.L) (U.input w) i M
    swap; · have hN:= hr hQ; exact ⟨Or.inl hN,hN.climb (le_mul_of_one_le_left (hx i) ht.always) le_rfl⟩
    rw [if_pos hQ] at ht'; refine ⟨?_,hs _ ht'⟩
    have hp:=hQ.1
    by_cases he':Shell.Inside (siteH i S.ratio) U.seeds (18*m)
    · obtain ⟨k,hk,h⟩:=halo_spec.mp he'; refine Or.inr ⟨mem_filter.mpr ⟨mem_univ _,hp⟩,k,halo_spec.mpr ⟨_,marks i S.ratio m (halo_subset _ _ (mem_singleton_self _)), (separation_comm ..).trans_le (h.trans ?_)⟩,hk,h⟩; change 18*m ≤30*m; omega
    refine Or.inl (hs _ ?_); apply le_trans (show ‖token c N R' q‖ ≤ Real.exp z-1 from Cove.bought _ _ _ (hW F U hz he hh i hp he' w H₀)); rw [show shells G₁ N M R' z i=z from if_pos hp]; exact fastR _ ht.profit.le ((show shells G₁ N M R' z i = z from if_pos hp) ▸ ht.expR i)
open Jets.Touch Sun Bay Pine Garden
-- use SAME Optional suppliers Y after thresholded Halo. don't presume CardT upgrade lengths built-in.
lemma paysLong (P:Teller su)(L:Side)(j i K m B N p₀:ℕ)(u v w q t θ D η γ:ℝ)(hh:0 < η)(hp:η<t):∀ᶠ x:ℝ in atTop, let h:=highW L u θ x; let Z:=coreRate L x; ∀ (f c:Side) (X:Flight j i)(e:f.val=c.val*X.L.val)(A:Plan i)(X':Run.St f)(Ω:ℕ → Atom su 2)(a b:ℝ),∀ U:Swathe X e X' Ω A a b t w q B,∀ (Y:Varn f c → Support c),
    X.L=L → 0 < b →0 < h → reserve η v (conversion (sliceL X e) m) D → (∀ i,Y i⊆enlargement (sliceL X e) m (radiusB x) (payT (sliceL X e) (radiusB x) i)) →
    let w i:= Real.exp 1*Port.shells U N (radiusB x) h Z i
    Ac.Hit Y (radiusB x) w v (betaF su x L^(-(3/8):ℝ)) → Ac.Hit Y (radiusB x) (tailTax (fun i=>waxV i≠none) w (betaF su x L^ (2:ℕ))) v (2*betaF su x L^(-(3/8):ℝ)):=by
   let f x:=loftCost w q N B (radiusB x) (highW L u θ x) t η
   have he(s:ℝ): Rate su L s f:= Port.funding L N p₀ B θ w q t η u γ hp s
   let Jg x:= rem L m (radiusB x) v (2*0*Real.exp η+f x) D
   let y x:= betaF su x L^(2:ℕ); let w x:= y x*(Real.exp 1*Jg x)
   have hm: Rate su L (-1) w:=by
      unfold w y; apply (Rate.mul (Rate.hat.pow 2) (Rate.mul_left (_:Rate su L (-3) Jg) _)).weaken (by norm_num)
      unfold Jg; simp_rw [mul_zero, zero_mul, zero_add,leeway L (f _)]; exact ((earned m v D).ruled.mul (he (-3))).weaken (by norm_num)
   filter_upwards [hm (-(3/8)) (by norm_num),Delay.shift_pos su L,Work.E01.radiusB_tendsto.eventually_ge_atTop (B+1)] with x hX ht hz
   intro h Z f c X F A X' Ω a b U Y he hB hv' hS hY v' hk
   let g i:= Port.shells U N (radiusB x) h 0 i; have hG i:0 ≤ g i:=by unfold g Port.shells; split; exact le_rfl; exact grew U i hB hv'
   let vv i:= Real.exp 1*g i; let p i:= y x*vv i
   have hp : Ac.Hit Y (radiusB x) p v (w x):=by
       have hx := offers (orbitM (sliceL X F)) Y g (fun i=>cared ..) hY hG (sky_hits U N (radiusB x) hp.le (by omega) hh.le (le_refl 0) hB hv') (by omega) (by omega) hS
       rw [show (sliceL X F).count=L from he] at hx
       exact heights_factor (y x) _ _ _ (heights_factor (Real.exp 1) _ _ _ hx (show ∀ i,vv i=_ from fun i=>rfl) (Real.exp_pos _).le) (fun i=>rfl) (by unfold y; positivity)
   have he : 0 < Z:=Real.rpow_pos_of_pos ht _; have hv i: 0 ≤ v' i := mul_nonneg (Real.exp_pos _).le (by unfold Port.shells; split; exact he.le; exact grew U i hB hv')
   have hh :0 ≤ y x:=by positivity -- unfold
   rw [two_mul]; intro x; refine budget_mono (budget_plus (hk x) (budget_loosen (hp x) ((le_abs_self _).trans hX))) (fun i=>?_) (fun i=> ?_)
   · split; swap; · exact le_rfl
     apply mul_nonneg _ (Real.exp_pos _).le; unfold tailTax; split; exact mul_nonneg hh (hv i); exact hv i
   split
   next hx=> unfold tailTax; split
             next he=> rw [show p i=_*_ from rfl,show vv i=v' i from congr_arg _ ((show g i= level U _ _ _ i from if_neg he).trans (if_neg he).symm)]; exact le_add_of_nonneg_left (mul_nonneg (hv i) (Real.exp_pos _).le)
             next he=> exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hh (mul_nonneg (Real.exp_pos _).le (hG _))) (Real.exp_pos _).le)
   next ht=> simp
-- note need bring χ/sigma reserve η and density response too.
open Sway OrbitG
lemma liquid (H' :Cash W τ μ L Q o C T (trimP T R δ β b))(Y:Send S.ratio N D)(X:Rise f N E K)(F:Fj D E K →Support c)(A q v:ℝ)(χ:Chi)(j:ℕ) [Fintype D][Countable E][Countable K]{m:D→ℝ}{h w:ℝ}{Λ:ℝ}{t:E→ℝ}{a:K→ℝ} (he: Peak Y R.threshold h v w m) (ht:Cents X t a h R.threshold) (hf:X.Wave R.threshold)(hp:0<δ)(hv': 0 ≤ q) :
   let U:= deckHue H' Y X F; Honest U A 0 q (mintD H' Y X F m t a w) v Λ χ j (fun _=>0) ∅ 0 0:=by
     intro U; let f₀:= mintD H' Y X F m t a w
     have hv i (W:Grid f)(V): ‖token c N v (U.works i W V)‖ ≤ f₀ i:=by
        let p:= δ⁻¹ ^ budget X i.val; have hm :0≤p:=by unfold p; positivity
        change ‖token c N v (p • (hue Y X R.threshold i.val W))‖ ≤ _; rw [map_smul,norm_smul,Real.norm_of_nonneg hm]; exact mul_le_mul_of_nonneg_left (pinches Y X he ht hf W i.property) hm
     have hG i:0 ≤ f₀ i:=(norm_nonneg _).trans (hv i 1 1)
     refine ⟨hG,le_rfl,hv',?_,by simp⟩
     intro T' Z h hU hh hg E _ _ _ x V z hx hh' i hF
     intro K ; have hp: 0≤King.windy U 0 i:=(zero_mul _).ge; have he: Brush j (f₀ i) (King.windy U 0 i) K x:= (Brush.certified hp (wearK c N v (U.works i _ (V x)))).climb (hv i _ (V x)) le_rfl
     exact ⟨Or.inl he,he.climb (le_mul_of_one_le_left (hG i) (Real.one_le_exp hv')) le_rfl⟩
end YM.QCD.Loom
