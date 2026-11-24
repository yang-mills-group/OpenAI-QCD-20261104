import YM.QCD.Loom.Signs
/-! # tan estimates. -/
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
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R :Rep su f}{s : Ratio c f}
variable {H:Cash W τ μ L Q o C T R}{N m l n:ℕ}
variable {X: Run.St c}{Γ: Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)}{η p b a θ:ℝ}
variable (h:Pack id id η p n X b Γ Y)
lemma drawnE (G:Land c (Site c) (Site c))(A B:Grid c)(m:ℕ)(v:Gaze c)(i j): cell (sheetP G m v A-sheetP G m v B) i j = sale v.1 i j (chipK v.1 m G i j v.2 (Kit.settled A)-chipK v.1 m G i j v.2 (Kit.settled B)):=by
   change cell (sheetP G m v A) i j-cell (sheetP G m v B) _ _=_; unfold sheetP; rw [stack,stack,monotype]; exact Eq.symm <| smul_sub ..
lemma flowerD (N:ℕ)(u:Grid f)(V:Grid c)(x:Gaze c)(h':Land c (Site c) (Site c))(hp:0<a)(v w: Site c→ℝ)
  (hv:∀ i,‖chipK x.1 m h' x.1 i x.2 (Kit.settled V)-chipK x.1 m h' x.1 i x.2 (Kit.settled (lowC s u))‖≤ v i)(hw:∀ i,‖chipK x.1 m h' i x.1 x.2 (Kit.settled V)-chipK x.1 m h' i x.1 x.2 (Kit.settled (lowC s u))‖≤w i) :
  ‖token c N a (dropG N h' s m x u V)‖ ≤ a^2*fingers N^2*((∑ i,v i)+∑ i,w i):=by
   rw [pulse]; let t:= sheetP h' m x V-sheetP h' m x (lowC s u)
   apply (fauna (Lat.copies N (-t)) hp).trans
   refine farm t x.1 v w (fun i=> (norm_nonneg _).trans (hv i)) (fun i=> (norm_nonneg _).trans (hw i)) ?_; intro i j; unfold t; rw [drawnE]; split
   next he=>
     subst i; split
     next h=> exact ((sold ..).trans (hv j)).trans (le_add_of_nonneg_right ((norm_nonneg _).trans (hw _)))
     next h=> rw [add_zero]; exact (sold ..).trans (hv j)
   next he=> split
             next h=> subst j; rw [zero_add]; exact (sold ..).trans (hw i)
             next h=> unfold sale; rw [if_neg (Ne.symm he),if_neg (Ne.symm h)]; simp

def gala (Y:Pays c (Site c) (Site c))(v: Gaze c)(m N:ℕ)(a:ℝ) : ℝ:= a^2*fingers N^2*(∑ i:Site c,(2*Port.crease v.1 m Y v.1 i v.2 + 2*Port.crease v.1 m Y i v.1 v.2))
include h
lemma galaN (v:Gaze c)(m N:ℕ)(a:ℝ):0≤gala Y v m N a:=by unfold gala; exact mul_nonneg (by positivity) (sum_nonneg fun i _=> add_nonneg (mul_nonneg zero_le_two (cups h ..).1) (mul_nonneg zero_le_two (cups h ..).1))
lemma galaP (Z:Gaze c)(m N:ℕ)(u:Grid f)(V:Grid c)(ha:0<η)(hx:0<a):‖token c N a (dropG N Γ S.ratio m Z u V)‖≤gala Y Z m N a:=by
    have he (i j): ‖chipK Z.1 m Γ i j Z.2 (Kit.settled V)-chipK Z.1 m Γ i j Z.2 (Kit.settled (lowC S.ratio u))‖ ≤2*Port.crease Z.1 m Y i j Z.2:=by
       rw [two_mul]; apply (norm_sub_le ..).trans; exact add_le_add ((cups h ..).2.2.2.1 _ (Run.citizenship c ha V)) ((cups h ..).2.2.2.1 _ (Run.citizenship c ha (lowC S.ratio u)))
    unfold gala; rw [sum_add_distrib]; exact flowerD N u V Z Γ hx _ _ (he _) (fun i=>he i _)
lemma galaSun (i:Site c)(m:ℕ) (N:ℕ) (hP:0≤p):gala Y (i,none) m N a≤ a^2*fingers N^2*(4*b):=by
   unfold gala; apply mul_le_mul_of_nonneg_left _ (by positivity); simp_rw [Finset.sum_add_distrib,← Finset.mul_sum]
   have hH:(∑ t,Port.crease i m Y i t none)≤ b:= (sum_le_sum (fun j _=> coins h i m i j hP)).trans (h.spends i)
   have hK:(∑ t,Port.crease i m Y t i none)≤ b:=(sum_le_sum (fun j _=> coins h i m j i hP)).trans (h.dues i)
   linarith
lemma lookout (x i j:Site c) (g:Lat.Frame c) (m:ℕ)(u v:Grid c)(d:ℝ)(hp:‖Kit.settled (Fork.rider (gauge g u) m x)- Kit.settled 1‖≤d)(hq:‖Kit.settled (Fork.rider (gauge g v) m x)- Kit.settled 1‖≤d)(he:d<η/2)(hu:0<η):
  ‖chipK x m Γ i j none (Kit.settled u)-chipK x m Γ i j none (Kit.settled v)‖≤ (2*d/(η/2))*Port.crease x m Y i j none :=by
    let f:=chipK x m Γ i j none; let w:=Port.crease x m Y i j none
    have hE:= trimming h x m i j; have hM p: f (Kit.settled (Fork.rider (gauge g p) m x))= Lat.touch (colour (g i))* f (Kit.settled p)*star (Lat.touch (colour (g j))):= (hE.2.2.2.2.1 _ _ (Fork.fit x m)).symm.trans (hE.2.2.2.2.2 p g)
    have hf (X:Grid c)(h:‖Kit.settled X-Kit.settled 1‖ ≤ d): ‖f (Kit.settled X)- f (Kit.settled 1)‖ ≤ w/(η/2)*d:=by
       have H (y)(h: y∈ Metric.ball (Kit.settled (1:Grid c)) η): y ∈ Kingdom c η:= Set.mem_iUnion.mpr ⟨1,h⟩
       apply (Run.lastwig f hu (fun i hi=>hE.2.2.1 _ (H i hi)) (fun i hi=>hE.2.2.2.1 _ (H i hi)) (show Kit.settled X∈ Metric.ball (Kit.settled (1:Grid c)) (η/2) from Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact h.trans_lt he))).trans
       exact mul_le_mul_of_nonneg_left h (div_nonneg hE.1 (half_pos hu).le)
    let U:= Fork.rider (gauge g u) m x; let V:= Fork.rider (gauge g v) m x
    have hx: ‖f (Kit.settled u) - f (Kit.settled v)‖= ‖f (Kit.settled U)- f (Kit.settled V)‖:=by unfold U V; rw [hM,hM,← sub_mul,← mul_sub]; exact (TouchConserve ..).symm
    calc _ = _ := hx
         _ ≤ ‖f (Kit.settled U)- f (Kit.settled 1)‖+ ‖f (Kit.settled V)-f (Kit.settled 1)‖:=by convert dist_triangle (f (Kit.settled U)) (f (Kit.settled 1)) (f (Kit.settled V)) using 1; rw [dist_eq_norm]; rw [dist_comm (f (Kit.settled 1)),dist_eq_norm,dist_eq_norm]
         _ ≤ _ := (add_le_add (hf U hp) (hf V hq)).trans_eq (by unfold w; ring)
lemma galaSky (O:Site c) (B N m:ℕ) (Y':Coat T F) (z: Directions su f)(p':ℝ)(g: Lat.Frame c)(w: LogField su c)
   (d0:ℝ)(hp:0<a)(hv:0≤p)(hh:0<η) (hB:Blanket S (Y'.input z) Y'.V O B g w p') (hE:0≤d0) (hK:∀ x:su.El,‖colour x-1‖≤d0* su.chord x)(ht:0≤p')(hd:d0*(S.ratio.count.val*p')<η/2)(hm:m+S.ratio.count.val+1 ≤ B) :
    let d:= d0*(S.ratio.count.val*p'); ‖token c N a (dropG N Γ S.ratio m (O,none) (Y'.input z) Y'.V)‖ ≤ a^2*fingers N^2*(4*d/(η/2)*b):=by
       intro d; have hD:0≤d:=by unfold d; positivity
       have he: (1:ℝ)≤S.ratio.count.val:=Nat.one_le_cast.mpr S.ratio.count.property
       have hV: ‖Kit.settled (Fork.rider (gauge g Y'.V) m O) -Kit.settled 1‖≤d:= Fork.renting _ O d m hD (fun i hi=> (hK _).trans (mul_le_mul_of_nonneg_left ((hB.coarse i (by omega)).trans (le_mul_of_one_le_left ht he)) hE))
       let U:=lowC S.ratio (Y'.input z)
       have hU: ‖Kit.settled (Fork.rider (gauge g U) m O)-Kit.settled 1‖≤d:= Fork.renting _ O d m hD (fun i hi=> (hK _).trans (mul_le_mul_of_nonneg_left (actingL O Y' z p' B m g w hB hm i hi) hE))
       let M₂ := 2*d/(η/2); have h₂ : 0 ≤ M₂:=by unfold M₂; positivity
       have hd i j:= lookout h O i j g m _ _ _ hV hU hd hh
       apply (flowerD N _ _ (O,none) Γ hp _ _ (hd _) (fun i=>hd i O)).trans; apply mul_le_mul_of_nonneg_left _ (by positivity)
       change (∑ i,M₂*Port.crease O m Y O i none)+(∑ i,M₂*Port.crease O m Y i O none) ≤ _; rw [← Finset.mul_sum,← Finset.mul_sum]; exact le_trans (add_le_add (mul_le_mul_of_nonneg_left ((sum_le_sum (fun j _=> coins h O m O j hv)).trans (h.spends _)) h₂) (mul_le_mul_of_nonneg_left ((sum_le_sum (fun j _=> coins h O m j O hv)).trans (h.dues _)) h₂)) (le_of_eq (by unfold M₂; ring))
end YM.QCD.Loom
