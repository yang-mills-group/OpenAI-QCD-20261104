import YM.Mural.Grow
import YM.Mills.Pearls
/-! # controlling height weights when a spin source appears. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon QCD.Mural
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
open QCD.Mural QCD.Loom.Fleet QCD.Anomaly NormedSpace
variable {K:ι→Site c}{w:ι→ℝ}{s:Finset ι}{a v r:ℝ}{m i n:ℕ}
variable (Y: Fleet H ι N)(Z:Finset (Keys c N))
lemma riseFee (j:ι)(X:Coat T F)(z:Air f su): ‖paidM Z v n a (Y.coming j X z)‖ ≤ ‖paidM Z v n a (Y.works j (X.input (X.liftA R.beta z)) X.V)‖:=by unfold coming; rw [map_smul,norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) ((Real.norm_of_nonneg (X.conserve ..).1).trans_le (X.conserve ..).2)
lemma two_slots (b:EvenA c N)(h:0<a)(hv:1 ≤ v)(hp:b.val ∈ Rim univ 2): ‖paidM Z v n a b‖≤ v^2* ‖token c N a b‖:=by
   rw [Mural.payment,Mural.sheet _ _ _ _ hv (fun _=>h),QCD.Loom.pulse, Creek.dry (fun _=>a) (fun _=>h),mul_sum]; refine sum_le_sum fun j _=>?_
   by_cases he : Grass.coef j b.val=0
   · simp only [show Grass.coef j (Cove.light _ b)=0 from he,norm_zero,zero_mul,mul_zero]; -- other?
     exact le_rfl
   have hx : premium Z v n j ≤ v^2:=by unfold premium; apply pow_le_pow_right₀ hv; exact (min_le_right _ _).trans ((Finset.card_le_card Finset.inter_subset_left).trans (hp j he).2)
   calc _ ≤ v^2*‖Grass.coef j (Cove.light (Keys c N) b)‖*load (fun _=>a) (mono j):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) (load_nn ..)
        _ = _ := by rw [ticket_mono _ _ (fun _=>h)]; ring
lemma ontoH (X:EvenA c N)(Λ:ℝ)(h:0<a)(hv:1≤v)(hp:X.val∈ Rim univ 2)(hV: ‖token c N a X‖ ≤ Λ)(hΛ:v^2 * Λ ≤1) : ‖paidM Z v n a (NormedSpace.exp X-1)‖ ≤ v^2 * (Real.exp 1*Λ):=by
   have hh:‖paidM Z v n a X‖ ≤ _:= (two_slots Z X h hv hp).trans (mul_le_mul_of_nonneg_left hV (sq_nonneg _))
   exact (Mural.spicy _ _ _ _ hv (fun _=>h) _ _ (show repay Z v n _ _ ≤ v^2*Λ from hh)).trans ((Port.fastR _ ((norm_nonneg _).trans hh) hΛ).trans_eq (by ring))
structure Stern (Y:Fleet H ι N) (F:Tree.Forest S.ratio)(Z:Finset (Keys c N))(k:ι→Site c)(w:ι→ℝ)(a v:ℝ)(s: Finset ι)(i j:ℕ)(X:ι→ Grid f→ Grid c→ EvenA c N): Prop where
   shape x U V : Y.works x U V = NormedSpace.exp (X x U V) -1
   stature x U V : (X x U V).val ∈ Rim univ 2
   theft : Y.Theft F k (fun i=> Real.exp 1*w i) a v s i j
   wage :0≤ w
   flare j :∀ U:Coat T F,U.x=τ→U.width=o.K→ U.manifest → ∀ z:Air f su,Y.riseP U z j≠0→ w j <‖token c N a (X j (U.input (U.liftA R.beta z)) U.V)‖→ j∈s ∧ ∃ x∈Y.ground j,x∈U.seeds.place ∧ separation x (k j) ≤ i
variable {Ψ:ι→ Grid f→ Grid c→EvenA c N}{γ:ℝ}
lemma seasoned (hv:Stern Y F Z K w a r s i m Ψ)(h:0<a)(hG:1 ≤v)(hM:v^n*Real.exp r ≤ Real.exp γ)(hp:∀ i,v^2*w i≤1): Vigil Y Z F K (fun j=> v^2*(Real.exp 1 *w j)) v n a γ s i m:=by
   let hZ:= hv.theft; have hg:0≤γ:= Real.one_le_exp_iff.mp (show 1≤Real.exp γ from (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hG) (Real.one_le_exp hZ.rate)).trans hM)
   let p j:=v^2*(Real.exp 1*w j); let A:=paidM Z v n a; have hX:0 ≤ p:=fun i=> mul_nonneg (sq_nonneg _) (hZ.grow i)
   refine ⟨hg,hX,hZ.pack,?_,?_⟩
   · intro j U hy hb ht z hz; have he:Y.riseP U z j≠0:=by intro he; unfold coming at hz; rw [he,zero_smul,map_zero,norm_zero] at hz; exact not_lt_of_ge (hX _) hz
     apply hv.flare j U hy hb ht z he; by_contra! hk
     have hu:= hz.trans_le (riseFee Y Z ..); rw [hv.shape] at hu; exact not_lt_of_ge (ontoH _ _ _ h hG (hv.stature j _ _) hk (hp j)) hu
   intro j U hy ht hh z; let X:= Y.coming j U z
   have hq: v^n * ‖token c N a X‖ ≤ Real.exp γ*p j:=by
       calc
         _ ≤ v^n*(Real.exp r*(Real.exp 1*w j)):=mul_le_mul_of_nonneg_left (hZ.deck j U hy ht hh z) (pow_nonneg (zero_le_one.trans hG) n)
         _ ≤ Real.exp γ*(Real.exp 1*w j):= by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hM (hZ.grow _)
         _ ≤ _:=mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hZ.grow _) (one_le_pow₀ hG)) (Real.exp_pos _).le
   exact (Mural.stamp _ _ _ (fun _=>a) hG (fun _=>h) _).trans hq
lemma kid (x:Sheet c): (paleF N x).val ∈ Rim univ 2:=by
   refine Submodule.sum_mem _ fun i _=>Submodule.sum_mem _ fun j _=>Submodule.smul_mem _ _ (Rim.multiply (Rim.atoms (mem_univ _)) (Rim.atoms (mem_univ _))) -- order
-- Varn component. 
variable {δ b:ℝ}(H:Cash W τ μ L Q o C T (trimP T O δ β b))
local notation "B"=>radiusB τ
variable {j k l:ℕ}{U: Flight j k}{d:f.val=c.val*U.L.val}
variable {Φ:Run.St f} {W':ℕ→Atom su 2}{J':Plan k}{η ξ p p' z R' u:ℝ}
local notation "V"=> sliceL U d
variable (G:Swathe U d Φ W' J' u v η p p' n)
local notation "PI"=> (VarnC H G N)
lemma stilt (h: S.ratio=V)(Z:Finset (Keys c N))(ht : RentP G N B (fiery su τ S.patch.L) z R' (wear L τ))
    (hW:∀ (Y:Coat T F), Y.x=τ→Y.width=o.K→Y.manifest →∀ i:Varn f c,waxV i= none →¬Inside (siteH i S.ratio) Y.seeds (18*B) →∀ w: Air f su, ((PI).riseP Y w i)≠0 → load (fun _=> R') (Cove.light _ (sliceF G N B i (Y.input (Y.liftA β w)))) ≤ z): Stern PI F Z (fun i=>siteH i S.ratio) (Port.shells G N B R' z) R' (fan L (1/4) τ) (univ.filter fun j:Varn f c=> waxV j=none) (18*B) (S.ratio.count.val^4+1) (fun i x _=> sliceF G N B i x):=by
       refine ⟨fun _ _ _=> rfl, ?_, metered H G h ht hW,(fun i=>?_),?_⟩
       · rintro (j|j) X Y
         · exact Submodule.smul_mem _ _ (Rim.one _)
         exact kid _ -- neg?
       · unfold Port.shells; split; exact ht.profit.le; exact grew G _ ht.growth ht.toll
       intro i Y hx hy he w hp hz; have hf:= lux G N B (Y.input (Y.liftA β w)) ht.growth ht.toll i
       have hK:waxV i=none:=by_contra fun h=> not_lt_of_ge hf ((if_neg h : Port.shells G N B R' z i = _).symm ▸ hz) -- defeq?
       refine ⟨mem_filter.mpr ⟨mem_univ _,hK⟩,?_⟩
       have hh:Inside (siteH i S.ratio) Y.seeds (18*B) :=by
          by_contra h; rw [Port.shells,if_pos hK] at hz; exact not_lt_of_ge (hW Y hx hy he i hK h w hp) hz
       obtain ⟨k,hk,h⟩:=halo_spec.mp hh; exact ⟨k,halo_spec.mpr ⟨siteH i S.ratio,Loom.marks i _ _ (halo_subset _ _ (mem_singleton_self _)),(separation_comm ..).trans_le (h.trans (by omega))⟩,hk,h⟩ -- orientation? halo_spec
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.stilt
#print axioms YM.MassiveQCD.Apron.seasoned
