import YM.Mural.Tress
/-! # Rotation palettes: use Mat defining representation. Fits any strata t tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open MassiveQCD MassiveQCD.Apron.Grove Plette Lat
open PaletteT Ribbon
variable {c f:Side}{j k m:ℕ}
abbrev Rank:=Hue × Hue
variable (x y:Site c)
noncomputable def breadth (g:Lat.Frame c)(u v:Rank) := star (colour (g y)) v.2 u.2 * colour (g x) u.1 v.1
noncomputable def fieldD (g:Lat.Frame c): PaletteT.Delta Rank:= fun i j=> match i with
 | none=> if j=none then 1 else 0
 | some k=> match j with | some v=> breadth x y g k v| none=> 1-∑ j : Rank, breadth x y g k j
local notation "Cx"=> colour
lemma sum_f (g:Lat.Frame c): PaletteT.straight (fieldD x y g):=by
    intro i; cases i with
    | none=> simp [fieldD]
    | some k=> change _= _; rw [Fintype.sum_option]; unfold fieldD; simp
lemma guardOne {N:ℕ}(i:Option Rank)(D: Option Rank→ MassiveQCD.Stitch.Tine c N Unit): aggregate (fun j=>fieldD x y (fun _=>1) i j) D = D i :=by
    unfold aggregate; have h(k l:Rank): breadth x y (fun _=>1) k l= if k=l then 1 else 0:=by
         unfold breadth; rw [show colour 1=1 from su.mat_one,star_one]; split
         · rename_i he; rw [he,Matrix.one_apply_eq,Matrix.one_apply_eq,one_mul]
         next he=>
            by_cases h:k.1=l.1; · rw [Matrix.one_apply_ne (show l.2≠k.2 from fun hv=> he (Prod.ext h hv.symm)), zero_mul]
            rw [Matrix.one_apply_ne h,mul_zero]
    cases i with
    | none=> simp [fieldD]
    | some i=> rw [Fintype.sum_option]; simp [fieldD,h]
noncomputable def cellD (p: Option Rank)(T:Mat):ℂ:=match p with
 | none=> 0
 | some k => T k.1 k.2
lemma knots (g:Lat.Frame c)(X:Mat)(i:Option Rank): cellD i (colour (g x) * X * star (colour (g y)))=∑ j:Option Rank, fieldD x y g i j * cellD j X:=by
   obtain _|p:=i; · simp [fieldD, cellD]
   rw [Fintype.sum_option]; unfold cellD fieldD; simp only [mul_zero,zero_add]; rw [Fintype.sum_prod_type]; simp only [Matrix.mul_apply, breadth, Finset.sum_mul]; rw [Finset.sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; ring
-- orthogonality Ward.Photo on Mat action
lemma anew (A B:Mat)(g h: su.El): star (colour g)*(colour g*A*star (colour h)-colour g*B*star (colour h))*colour h=A-B:=by rw [← sub_mul,← mul_sub, mul_assoc, mul_assoc _ (star _) (colour h),show star (colour h)*colour h=(1:Mat) from su.mat_star_mul _,Matrix.mul_one,← mul_assoc,show star (colour g)*colour g=(1:Mat) from su.mat_star_mul _,Matrix.one_mul]
lemma leaseX (Z:Mat)(g h: su.El): ‖Z‖≤ ‖colour g*Z*star (colour h)‖:=by
    let X i:=colour i; let Y:= colour g*Z*star (colour h)
    have he: Z= (star (colour g))*Y* colour h:= by
       have ht:= anew Z 0 g h -- Anew doesn't take x
       simpa using ht.symm
    calc ‖Z‖= ‖star (colour g)*Y*colour h‖:= congr_arg norm he
         _ ≤ _ := (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (shadeC h)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((norm_star _).le.trans (shadeC g)))))
lemma place_limit : ∃ C:ℝ,0<C ∧∀ (X:Mat)(i j:Hue), ‖X i j‖ ≤ C* ‖X‖:=by
    let f(i:Rank): Mat→ₗ[ℂ]ℂ:= { toFun:=fun x=>x i.1 i.2,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
    let B i:= f i|>.toContinuousLinearMap; let z:=∑ i:Rank,‖B i‖; have hZ:0 ≤z:=sum_nonneg fun i _=>ContinuousLinearMap.opNorm_nonneg (B i)
    exact ⟨z+1, hZ.trans_lt (lt_add_of_pos_right _ zero_lt_one),fun X i j=>(B (i,j)|>.le_opNorm _).trans (mul_le_mul_of_nonneg_right ((single_le_sum (fun k (_:k∈univ)=>ContinuousLinearMap.opNorm_nonneg (B k)) (mem_univ (i,j))).trans (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _))⟩
-- carrier path without seam.S.Volume.B
noncomputable def cord (x y:Site c): Walk:= route 0 (Lattice.lift (y-x)) 1
lemma cord_end : stop x (cord x y)=y:=by unfold cord; rw [wrap_stop,route_end,wrap_lift]; abel
lemma cord_len (h: separation x y ≤ m): (cord x y).length ≤ 4*m:=by
   let a:= Lattice.lift (y-x); let l:= allAxes (1:Lattice.Order); let p:= separation x y
   have hp (i:Axis): (a i).natAbs ≤ m:=by
       apply le_trans (b:=separation y x) _ ((separation_comm y x) ▸ h); change (a i).natAbs ≤ Finset.univ.sup (fun i:Axis=> (a i).natAbs); exact Finset.le_sup (f:=fun i:Axis=> (a i).natAbs) (mem_univ i)
   have hh(k:List Axis): (axisRoute 0 a k).length ≤ k.length*m:=by
       induction k with
       | nil=>simp [axisRoute]
       | cons i k ih=> rw [show axisRoute 0 a (i::k)=Lattice.straight i (a i-0)++axisRoute 0 a k from rfl, List.length_append,List.length_cons,Nat.add_mul]; unfold Lattice.straight; simp only [List.length_replicate,sub_zero]; have hx:=hp i; omega
   change (axisRoute 0 a l).length≤4*m; have h:=hh l; simpa only [l, allAxes,List.length_map,List.length_finRange] using h
noncomputable def apogee (U:Grid c): Mat:= colour (travel U x (cord x y))
@[fun_prop] lemma goodwill : Continuous (apogee x y):=by unfold apogee; fun_prop
lemma lamp (V:Grid c): ‖apogee x y V‖≤1:= shadeC _
lemma clot (H: Lat.Frame c) (U:Grid c): apogee x y (gauge H U)=colour (H x)* apogee x y U*star (colour (H y)):=by unfold apogee; rw [travel_gauge,cord_end,colour_mul,colour_mul,colour_inv]
lemma remainsX : apogee x y 1=1:=by
    have ht (x: Site c)(w:Walk): travel (1:Grid c) x w=1:=by induction w generalizing x with
                                        | nil=>rfl
                                        | cons a w ih=> rw [travel,ih]; cases a with| mk d b=> cases b <;> simp [Step.read]
    rw [apogee,ht]; exact su.mat_one
end YM.QCD.Comet
#print axioms YM.QCD.Comet.guardOne
#print axioms YM.QCD.Comet.leaseX
#print axioms YM.QCD.Comet.cord_len
