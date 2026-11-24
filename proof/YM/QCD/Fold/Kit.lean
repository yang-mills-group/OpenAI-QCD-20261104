import YM.QCD.Fold.Pool
/-! # Packing over a smaller period with actual costs. Same troops biomass, maybe longer homeland tags. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D B b k:ℕ}(T:Window f F D)
-- analytic crop bridge
abbrev trayT (a:Tray f): Tray F := fun i=> a (T.cut i.1,i.2)
def copy (x:Pulse f) : Pulse F := (trayT T x.1,trayT T x.2)
lemma pose (U:Grid f): settled (T.links U)=copy T (settled U):=rfl
def copyL:Pulse f→L[ℂ]Pulse F:=LinearMap.toContinuousLinearMap {
 toFun:=copy T
 map_add' x y:=rfl
 map_smul' s x:=rfl
}
lemma pulse_bound (x:Pulse f): ‖copy T x‖≤‖x‖:=by
    have he (i:Tray f): ‖trayT T i‖ ≤ ‖i‖ := pi_norm_le_iff_of_nonneg (norm_nonneg i) |>.2 (fun j=> norm_le_pi_norm i _)
    unfold copy; rw [Prod.norm_def,Prod.norm_def]; exact max_le_max (he _) (he _)
lemma harriet {x:Pulse f}{r:ℝ}(hp:x∈Kingdom f r):copy T x∈Kingdom F r:=by
    obtain ⟨U,hU⟩:=Set.mem_iUnion.mp hp; refine Set.mem_iUnion.mpr ⟨T.links U,?_⟩; rw [Metric.mem_ball,dist_eq_norm,pose]; rw [Metric.mem_ball,dist_eq_norm] at hU; change ‖copyL T x-copyL T _‖<r; rw [← map_sub]; exact (pulse_bound ..).trans_lt hU
lemma kennel (U V:Grid f)(X:Support F)(hp:Agrees (X.image T.cut) U V):Agrees X (T.links U) (T.links V):=by
   intro i hi hj; apply hp _ (mem_image_of_mem _ hi); change T.cut i.1+step i.2∈ X.image T.cut; rw [← T.step_up]; exact mem_image_of_mem _ hj
lemma queue (U:Grid f)(W:Lat.Frame f):T.links (gauge W U)=gauge (W ∘ T.cut) (T.links U):=by funext i; simp [Lattice.gauge,T.step_up,Window.links] -- risky
lemma new_growth (x y :Site F)(S:Support F)(X:Pulse F→Bundle)(m r:ℝ)(h:Crop x y r S X m):Crop (T.cut x) (T.cut y) r (S.image T.cut) (X ∘ copy T) m:=by
   obtain ⟨ha,hb,hc,hd,hf,hg⟩:=h
   refine ⟨ha,fun hv=> ⟨mem_image_of_mem _ (hb hv).1,mem_image_of_mem _ (hb hv).2⟩,fun i h=> (hc _ (harriet T h)).comp i (copyL T).differentiableAt,fun i h=>hd _ (harriet T h),?_,?_⟩
   · intro U V H; simp only [comp_apply,← pose]; exact hf _ _ (kennel T U V S H)
   intro U g; simp only [comp_apply,← pose,queue,hg]
-- depends only T cut, height
variable (h:f.val∣ F.val)
local notation "π"=>Macrame.splitter h
variable {a e r w:ℝ}{x y:Site F}(p:ℂ)(b B:ℕ)
variable {Z:Support F}{X:Pulse F→Bundle}
def floret (c:Site F)(d:Site F)(x:Support F)(X:Pulse F→Bundle)(y:Support f) : Pulse f→Bundle:= loan h c d x b B y • p • (X ∘ copy T)
def flora (c:Site F)(d:Site F)(x:Support F)(A:ℝ)(y:Support f):ℝ:= loan h c d x b B y*A
lemma loan_crop (hp:‖p‖=1)(hx:(⇑π)=T.cut)(he:Crop x y a Z X r)(V:Support f): Crop (T.cut x) (T.cut y) a V (floret T h p b B x y Z X V) (flora h b B x y Z r V):=by
   let A:= loan h x y Z b B V; change Crop _ _ _ V (A • _) (A*_); by_cases hm:A=0; · rw [hm,zero_smul,zero_mul]; exact Crop.zero
   have hh:= glimpse h _ _ _ _ _ _ hm -- maybe
   obtain ⟨hi,hK,hQ⟩:= hh; have he' : Z.image T.cut ⊆V:=hx ▸ hi
   have hf:= Fork.wider_c (new_growth T x y Z X r a he) he'; have hN :0 ≤A:=cushion ..
   have hg:= ((hf.alloy p).alloy (A:ℂ)); rw [hp,one_mul,Complex.norm_real,Real.norm_of_nonneg hN] at hg; exact hg
lemma full_fl {Z:Support F}(X:Pulse F→Bundle)(x y:Site F)(hv:4*B+3<f.val): (∑ V, floret T h p b B x y Z X V)=p • (X ∘ copy T):=by unfold floret; rw [← sum_smul,purse h x y Z b B hv,one_smul]
lemma full_f {Z:Support F}(x y:Site F)(hv:4*B+3<f.val)(hr:0≤r)(he:0≤e): ∑ V, rent e b V*flora h b B x y Z r V ≤ rent e b Z*r :=by
   have hv:=purse h x y Z b B hv; unfold flora; refine (sum_le_sum (g:=fun V=> rent e b Z * (loan h x y Z b B V *r)) (fun i _=>?_)).trans_eq ?_
   · by_cases he':loan h x y Z b B i=0; · rw [he']; simp
     exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (glimpse h _ _ _ _ _ _ he').cheap) he)) (mul_nonneg (cushion ..) hr)
   rw [← mul_sum,← sum_mul,hv,one_mul]
lemma zip_fl (U:Grid f)(o:Site F)(hp:o=x ∨ o=y)(hv:4*B+3<f.val)(hz:0<a)(he:Crop x y a Z X r)(hx:(⇑π)=T.cut): (∑ i∈shortZip (T.cut o) B, floret T h p b B x y Z X i (settled U))= if Z∈shortZip o B then p • X (settled (T.links U)) else 0:=by
   by_cases hX:r=0
   · have hg :X (settled (T.links U))=0:= norm_eq_zero.mp (le_antisymm (hX ▸ he.2.2.2.1 _ (citizenship F hz (T.links U))) (norm_nonneg _)); simp [floret,← pose,hg]
   have hK:= he.2.1 hX; have hV i (hh:loan h x y Z b B i≠0): i∈shortZip (T.cut o) B ↔ Z∈shortZip o B:=by
      have hT := (glimpse h x y Z b B i hh).site hK.1 hK.2 o (mem_insert.mpr (hp.imp_right mem_singleton.mpr)); unfold shortZip; rw [← hx]; simpa only [Finset.mem_filter,mem_univ,true_and] using hT.symm
   split
   next hZ=>
     rw [sum_subset (subset_univ _) (fun i _ hi=>?_),← Finset.sum_apply,full_fl T h p b B X x y hv]; rfl
     unfold floret; rw [show loan h x y Z b B i=0 from by_contra fun hw=>hi ((hV i hw).2 hZ),zero_smul]; rfl
   next hZ=>refine sum_eq_zero fun i ht=>?_ ; unfold floret; rw [show loan h x y Z b B i=0 from by_contra fun hw=>hZ ((hV i hw).1 ht),zero_smul]; rfl
end YM.QCD.Folding
