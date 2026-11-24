import YM.Helio.Tel
/-!
 Separation bill for bloom product paths. One endpoint root; terminal momentum leg insertion.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder Paths -- conflicts
variable (W:Bloom k)(i j: Walk)(o:Site c)
-- center and tail
noncomputable def windF (V:Pulse c) : Bundle:= shimmer (0:Site c) o i • touch (Leaf.Paths.pursueP V o i)
local notation "N'"=> Push.AbsoluteSums.Paths.native o i
lemma wx0 : o∈ N':=by unfold Push.AbsoluteSums.Paths.native; rw[List.mem_toFinset]; cases i <;> simp [Lattice.visits]
lemma wxE: stop o i∈ N':=by unfold Push.AbsoluteSums.Paths.native; rw[List.mem_toFinset]; induction i generalizing o with| nil=>simp[Lattice.visits,stop]|cons a i ih=> exact List.mem_cons_of_mem o (ih _)
lemma woS (X:Grid c): windF i o (settled X) = winding o i 0 X:=by unfold windF; rw [pursuit]; rfl
open Metric
lemma coiled (X:Grid c): ‖windF i o (settled X)‖≤1:=by
    rw [woS]; unfold winding; rw [norm_smul]; have h:‖shimmer 0 o i‖=1:=by rcases Stew.glisten (0:Site c) o i with h|h <;> simp[h] -- edit
    rw[h,one_mul]; exact Lat.rotation_price (touch_u ⟨su.mat_star_mul _,su.mat_mul_star _⟩)
lemma paidC (h:0 < t)(he:0 < σ)(hv:t≤Real.exp σ-1): Crop o (stop o i) t N' (windF i o) (‖TouchL‖*Real.exp (σ*i.length)):=by
     refine ⟨by positivity,fun _=>⟨wx0 ..,wxE ..⟩,fun x _=> ?_,fun x hx=> ?_,fun x y h=> ?_,fun U g=>?_⟩
     · exact ((TouchL.differentiable.comp (reachP o i)).const_smul (shimmer 0 o i)).differentiableAt
     · obtain ⟨V,hV⟩:=Set.mem_iUnion.mp hx; rw [windF,norm_smul]; have hp:‖shimmer 0 o i‖=1:=by rcases Stew.glisten 0 o i with h|h <;> simp[h];
       rw [hp,one_mul]; rw [Metric.mem_ball,dist_eq_norm] at hV; apply (TouchL.le_opNorm _).trans; apply mul_le_mul_of_nonneg_left (le_trans (Leaf.Paths.pose x V i o hV.le) _) (norm_nonneg _); rw [mul_comm, Real.exp_nat_mul]; apply pow_le_pow_left₀ (by positivity); linarith
     · dsimp only [Function.comp_apply]; rw[woS,woS]; unfold winding; rw[show travel x o i=travel y o i from travel_local _ _ _ _ (fun k hk hh=>h k (List.mem_toFinset.mpr hk) (List.mem_toFinset.mpr hh))]
     rw [woS,woS]; unfold winding; rw [travel_gauge, Lat.colour_mul, Lat.colour_mul,Lat.colour_inv,touch_star,Matrix.mul_smul,Matrix.smul_mul,touch_mul,touch_mul]
local notation "s"=> stop o i
local notation "v"=> stop (stop o i) j
noncomputable def nursery : Support c:=(N'∪(twig W).footprint (s))∪ Push.AbsoluteSums.Paths.native (stop o i) j
noncomputable def episode (ξ:ℝ):= (windF i o*LeafM.transient W (s) ξ)*windF j (s)
local notation "Ξ"=> nursery W i j o
lemma nucleus : o∈ Ξ∧(s)∈ Ξ∧v∈ Ξ:= ⟨mem_union_left _ (mem_union_left _ (wx0 ..)),mem_union_left _ (mem_union_left _ (wxE ..)),mem_union_right _ (wxE j (s))⟩
-- rent no division by costs beyond k.
lemma expense (hb:0<B)(hη:0≤η)(ht:η/B ≤ t): rent η B Ξ ≤ Real.exp (η*(3+2*(k:ℝ))+t*((twig W).length+i.length+(j.length:ℝ))):=by
       let x:= Push.AbsoluteSums.Paths.native (stop o i) j; let U:= (twig W).footprint (stop o i); have hm: stop o i ∈ U:= Finset.mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩
       have hr(a:Site c)(l:Walk): rent η B (Push.AbsoluteSums.Paths.native a l) ≤ Real.exp (η+t*l.length):=by
             unfold rent; apply Real.exp_monotone; let Xℓ:=coverNumber B (Push.AbsoluteSums.Paths.native a l); change η*Xℓ ≤ _; have he:(B:ℝ)*(Xℓ:ℝ)≤ (B:ℝ)+(l.length:ℝ):=by exact_mod_cast Push.AbsoluteSums.Paths.native_cover (x:=a) hb l
             have hB:0 < (B:ℝ):=by exact_mod_cast hb
             apply le_of_mul_le_mul_right _ hB; nlinarith only [mul_le_mul_of_nonneg_left he hη, mul_le_mul_of_nonneg_right ((div_le_iff₀ hB).mp ht) (Nat.cast_nonneg (α:=ℝ) l.length)]
       have hx: rent η B Ξ ≤ rent η B N' * rent η B U *rent η B x :=by
            unfold rent; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; have h: coverNumber B Ξ ≤ coverNumber B N'+coverNumber B U+coverNumber B x:=le_trans (Lattice.Corona.meets_sum (mem_union_right N' hm) (wx0 j _) B) (Nat.add_le_add_right (Lattice.Corona.meets_sum (wxE i o) hm B) _)
            push_cast; simp only [←mul_add]; gcongr; exact_mod_cast h -- maybe order rw nested η
       apply hx.trans; apply (mul_le_mul (mul_le_mul (hr ..) (house W (s) hb hη ht) (Run.fair ..).le (Real.exp_pos _).le) (hr ..) (Run.fair ..).le (by positivity)).trans; rw[←Real.exp_add, ←Real.exp_add]; apply le_of_eq; congr 1; ring
-- analytic width crop. Bottle proof guarantee e≤... clipped
noncomputable def harvestK (σ c' ξ:ℝ):= (‖TouchL‖*Real.exp (σ*i.length)*cal W c' ξ σ)*(‖TouchL‖*Real.exp (σ*j.length))
lemma influenced (ξ c' δ S W':ℝ)(hB:Bottle S c' δ ξ)(hp: W.Spins)(hv:0≤ c')(hξ:0<ξ)(hw:0<W')(ht:0<S)(he:W'=δ*ξ^2)(h: W'≤Real.exp S-1) : Crop o (v) W' Ξ (episode W i j o ξ) (harvestK W i j S c' ξ):=by
       subst W'; exact ((paidC i o hw ht h).joined (trills W (s) hB hv hξ.le hp) hw).joined (paidC j _ hw ht h) hw
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.coiled
#print axioms YM.QCD.Entr.Meridian.expense
#print axioms YM.QCD.Entr.Meridian.influenced
