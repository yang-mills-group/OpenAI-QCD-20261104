import YM.Massive.Lining.Pinula
/-! # AP seam transmission from cover sampling to placements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker
open Purl Scan Cylinder
namespace Ferry
local notation "K" => starRingEnd ℂ
variable (n:Side)(u:Finset Cover)(b x:Cover)(s:Signed)
def gain (x:Cover): Site n:= wrap n (x+b)
abbrev belt (b:Cover): Whorl u (Site n):= lower b
def gap (x:Cover): ℂ:= ∏ a,(-1:ℂ)^(x a)
lemma gap_phase (s:Signed): gap (s.act x)=gap x:=by unfold gap; rw [← Equiv.prod_comp s.perm]; apply prod_congr rfl; intro i _; rw [Signed.act_at]; split; rw [neg_one_zpow_eq_ite,neg_one_zpow_eq_ite]; simp; rfl
lemma ap_pace (v:Cover) : ap n (x+n.val • v)= ap n x*gap v:=by
   unfold ap gap; rw [← prod_mul_distrib]; apply prod_congr rfl; intro i _; change (-1:ℂ)^((x i+n.val • v i)/(n.val:ℤ))=_; rw [nsmul_eq_mul, mul_comm, Int.add_mul_ediv_right _ _ (show (n.val:ℤ) ≠ 0 by exact_mod_cast n.property.ne'),zpow_add₀ (by simp)]
lemma sheet_unit (x: Site n) : wrap n (sheet x)=x:=by
   funext i; change ((↑((x i).val):ℤ): Per n)=_; push_cast; exact ZMod.natCast_zmod_val ..
lemma sheet_ref (x:Cover)(i:Axis): sheet (wrap n x) i=x i % (n.val:ℤ):= ZMod.val_intCast _
lemma sheet_pace (x : Site n) : ap n (sheet x)=1:=by
    unfold ap; rw [prod_eq_one]; intro i _; change (-1:ℂ)^((↑((x i).val):ℤ)/(n.val:ℤ))=_; have hv : ((x i).val:ℤ) < n.val:= by exact_mod_cast ZMod.val_lt (x i)
    rw [Int.ediv_eq_zero_of_lt (by positivity) hv,zpow_zero]
lemma sheet_launch : ap n x * ap n (s.act (sheet (wrap n x)))=ap n (s.act x):=by
   let y:Cover := sheet (wrap n x); let v:Cover:= fun i=> x i/(n.val:ℤ); have hv:y+n.val • v=x:=by funext i; unfold y; rw [Pi.add_apply, sheet_ref, Pi.smul_apply,nsmul_eq_mul]; exact Int.emod_add_mul_ediv (x i) n.val
   have hs:= s.act_add y (n.val • v); have hi: s.act (n.val • v)=n.val • s.act v:=map_nsmul s.actEquiv _ _; rw [hv,hi] at hs; change ap n x*ap n (s.act y)=_; nth_rw 1 [← hv]; rw [ap_pace,sheet_pace,one_mul,hs,ap_pace,gap_phase,mul_comm]
lemma ap_star : star (ap n x)=ap n x:=by unfold ap; simp
lemma ap_origin : ap n 0=1:= by simp [ap]
lemma table (b:Cover) : belt n u b=spar (fun i:↥u=>gain n b i.val) (fun i=> ap n (i.val+b) • 1):=by
   ext ⟨⟨i,a⟩,v⟩ ⟨⟨j,q⟩,w⟩; by_cases hw:v=w <;> by_cases hc:a=q <;> by_cases hk:wrap n (i.val+b)=j <;> simp [belt,lower,spar_intro,gain,hw,hc]
lemma belt_star (b:Cover): Mstar (belt n u b)=belt n u b:=by
   rw [table,spar_color]; congr 1; funext i; rw [mstar_smul,mstar_bulk,ap_star]
lemma roller (M:Spike) : Cylinder.Action.moved (n:=n) (F:=6) s M=spar (fun x:Site n=> s.act x) (fun x=> ap n (s.act (sheet x)) • wave M):=by
    ext ⟨⟨i,a⟩,w⟩ ⟨⟨j,b⟩,v⟩; by_cases h:s.act i=j <;> by_cases hh:w=v <;> simp [Cylinder.Action.moved, spar_intro, h,hh,← wrap_signed,sheet_unit,eq_comm]; aesop
lemma sails (hu: Parade u)(M:Spike): belt n u b * Action.moved s M= hu.spinT s M*belt n u (s.act b):=by
   rw [table, table,roller, Parade.spinT,spar_spar, spar_spar]; congr 1
   · funext i; simp only [gain, hu.frame_at, wrap_signed, Signed.act_add]
   funext i; rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]; apply congr_arg (fun p:ℂ=> p • wave M); simp only [gain,sheet_launch, Signed.act_add,hu.frame_at]
lemma sight (k:Frame n): Lat.rotates 6 k= spar id (fun i=> Lat.touch (Lat.colour (k i))):=by
   ext i j; by_cases h:i.2=j.2 <;> by_cases he:i.1.1=j.1.1 <;> simp [Lat.rotates,siteRot,spar_intro,copies,h,he, Matrix.blockDiagonal_apply,rides]
lemma ferries (k:Frame n): belt n u b * Lat.rotates 6 k= siteWard u (k ∘ gain n b) * belt n u b:=by
   rw [table,sight,siteWard,spar_spar,spar_spar]; apply congr_arg (spar _); funext i; rw [id_eq,Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]; rfl
lemma ferry_stretch (k:Frame n)(U:Grid n): expandAt (wrap n b) (gauge k U)=gaugeF (k ∘ gain n b) (expandAt (wrap n b) U):=by rw [expandAt_gauge]; congr 1; funext i; rw [Function.comp_apply,gain,map_add]
lemma wind (U:Grid n): expandAt (wrap n b) (pull s 0 U)=scene s (expandAt (wrap n (s.act b)) U):=by simp_rw [expandAt_pull, affine,add_zero, wrap_signed,scene]
lemma nocturne (U:Grid n) : expandAt (wrap n b) (conjugate ∘ U)= night (expandAt (wrap n b) U):=rfl
end Ferry
end YM.Massive.Lining
#print axioms YM.Massive.Lining.Ferry.sails
