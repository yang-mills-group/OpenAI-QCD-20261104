import YM.Massive.Lining.Daymark
/-! # Common stencil for gauge extractor and spin ports; generating nuclei. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open Purl Scan Cylinder Paper TensorProduct
variable {H:Source.Hol su}{d h:ℕ}(F:Flag H d h)(U: Kedge H d h)(t:Finset Cover)
local notation "Q" => SpinMode d
local notation "T" => Nearest t 6
local notation "D" => Cylinder.Formula t 6
structure Room : Prop where
   extends_box : box d⊆t
   parity : Parade t
   panel : Plane t F.F
   ports : ∀ x∈box d, Plane t (U.T x)
namespace Room
variable {t F U}
private lemma warmer {u v: Finset Cover}(h:u⊆v){X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]{f:Land→X}(hf:Plane u f): Plane v f:=fun q=> spread (hf q) h
lemma origin (h: Room F U t): 0∈t:=h.extends_box (center_box d)
theorem uniform (F:Flag H d h)(U: Kedge H d h) : ∃ t:Finset Cover, Room F U t:=by
    obtain ⟨t,hT,H₁,v⟩:= (((eventually_ge_atTop (box d))).and ((F.tight.planes).and ((eventually_all_finset _).mpr (fun (i:Cover) (_:i∈box d)=> (U.tight i).planes)))).exists -- implicit syntax
    let T':= Finset.univ.biUnion (fun s: Signed=> t.image s.act); have h : t⊆T':=fun i hi=> Finset.mem_biUnion.mpr ⟨1,mem_univ _,mem_image.mpr ⟨i,hi,Signed.act_one _⟩⟩
    have he(s:Signed)(x:Cover)(h:x∈T'):s.act x∈ T':=by obtain ⟨y,-,ht⟩:=mem_biUnion.mp h; obtain ⟨z,hw,rfl⟩:=mem_image.mp ht; exact mem_biUnion.mpr ⟨s*y,mem_univ _,mem_image.mpr ⟨z,hw,Signed.act_mul s y z⟩⟩
    refine ⟨T',fun i hi=>h (hT hi), ?_, warmer h H₁, fun i hi=> warmer h (v i hi)⟩; intro s; ext x; constructor; intro hu; obtain ⟨y,hy,rfl⟩:=mem_image.mp hu; exact he s y hy
    intro ht; exact mem_image.mpr ⟨_,he s⁻¹ x ht,s.act_inv x⟩
end Room

abbrev extraction (x:Land): Labels.Jet su:=Source.Drops.expand h (F.F x)
def ink (x:Land): QCD.Grass.Dirac Q →ₐ[ℂ] QCD.Grass.Dirac T:= Grass.adapter (start U t x) (Mstar (start U t x))
def glaze (x:Land): Pol d →ₗ[ℂ] Grass.Dirac T:= (TensorProduct.lid ℂ _).toLinearMap.comp (TensorProduct.map (Labels.read (extraction F x)).toLinearMap (ink U t x).toLinearMap)
lemma stencil (x:Land)(u:GPol)(y:SpinPol d): glaze F U t x (u ⊗ₜ[ℂ] y)=Labels.read (extraction F x) u • ink U t x y:=by rw [glaze,LinearMap.comp_apply,TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul]; rfl
lemma brush (hb:Room F U t) (u:GPol) : Work.G06.EntryPoly t (fun x:Land=> Labels.read (extraction F x) u):=by
   induction u using MvPolynomial.induction_on with
   | C a=> simp only [Labels.read,MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]; exact EPconst a
   | add p q hp hq=> simp_rw [_root_.map_add]; exact EPsum hp hq
   | mul_X p i hp=>simp_rw [_root_.map_mul]; apply EPprod hp; simp only [Labels.read,MvPolynomial.aeval_X]; exact hb.panel (Work.G05.snapCoord h i).toLinearMap
lemma etching (hb:Room F U t) (i:Q)(j:T): Work.G06.EntryPoly t (fun x:Land=>start U t x i j):=by
   unfold start; simp_rw [imprints]; by_cases ht: i.2=j.2; swap; · simp only [if_neg ht]; exact EPconst _
   simp only [if_pos ht,emboss,Matrix.smul_apply,smul_eq_mul,Lat.touch, kroneckerMap_apply]; by_cases he:j.1.1.val∈box d
   · apply EPprod (EPconst _); apply EPprod (EPconst _); exact Paper.plane_color _ (hb.ports _ he) _ _
   rw [ghost _ _ he]; simpa only [Complex.ofReal_zero, zero_mul] using EPconst (u:=t) 0 -- rew rw simp?
end YM.Massive.Lining.Temper
#print axioms YM.Massive.Lining.Temper.Room.uniform
