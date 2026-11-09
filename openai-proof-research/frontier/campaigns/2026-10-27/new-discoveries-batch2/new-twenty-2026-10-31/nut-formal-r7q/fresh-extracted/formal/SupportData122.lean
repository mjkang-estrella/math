import SignedCatalogue
import NewCertificates0180
import NewCertificates0181
import NewCertificates0182
import NewCertificates0183
import NewCertificates0184
import NewCertificates0185
import NewCertificates0186
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace Nut8.FiniteSupport122
noncomputable def e : Equiv.Perm (Fin 8) := checkedEquiv [0, 6, 7, 2, 1, 4, 5, 3] (by decide +kernel)
def p : Fin 8 → Fin 8 := ![0, 0, 0, 1, 2, 3, 4, 5]
def matrices : Finset QuotientMatrix := {NewCertificates0180.C5788, NewCertificates0180.C5789, NewCertificates0180.C5790, NewCertificates0180.C5791, NewCertificates0181.C5792, NewCertificates0181.C5793, NewCertificates0181.C5794, NewCertificates0181.C5795, NewCertificates0181.C5796, NewCertificates0181.C5797, NewCertificates0181.C5798, NewCertificates0181.C5799, NewCertificates0181.C5800, NewCertificates0181.C5801, NewCertificates0181.C5802, NewCertificates0181.C5803, NewCertificates0181.C5804, NewCertificates0181.C5805, NewCertificates0181.C5806, NewCertificates0181.C5807, NewCertificates0181.C5808, NewCertificates0181.C5809, NewCertificates0181.C5810, NewCertificates0181.C5811, NewCertificates0181.C5812, NewCertificates0181.C5813, NewCertificates0181.C5814, NewCertificates0181.C5815, NewCertificates0181.C5816, NewCertificates0181.C5817, NewCertificates0181.C5818, NewCertificates0181.C5819, NewCertificates0181.C5820, NewCertificates0181.C5821, NewCertificates0181.C5822, NewCertificates0181.C5823, NewCertificates0182.C5824, NewCertificates0182.C5825, NewCertificates0182.C5826, NewCertificates0182.C5827, NewCertificates0182.C5828, NewCertificates0182.C5829, NewCertificates0182.C5830, NewCertificates0182.C5831, NewCertificates0182.C5832, NewCertificates0182.C5833, NewCertificates0182.C5834, NewCertificates0182.C5835, NewCertificates0182.C5836, NewCertificates0182.C5837, NewCertificates0182.C5838, NewCertificates0182.C5839, NewCertificates0182.C5840, NewCertificates0182.C5841, NewCertificates0182.C5842, NewCertificates0182.C5843, NewCertificates0182.C5844, NewCertificates0182.C5845, NewCertificates0182.C5846, NewCertificates0182.C5847, NewCertificates0182.C5848, NewCertificates0182.C5849, NewCertificates0182.C5850, NewCertificates0182.C5851, NewCertificates0182.C5852, NewCertificates0182.C5853, NewCertificates0182.C5854, NewCertificates0182.C5855, NewCertificates0183.C5856, NewCertificates0183.C5857, NewCertificates0183.C5858, NewCertificates0183.C5859, NewCertificates0183.C5860, NewCertificates0183.C5861, NewCertificates0183.C5862, NewCertificates0183.C5863, NewCertificates0183.C5864, NewCertificates0183.C5865, NewCertificates0183.C5866, NewCertificates0183.C5867, NewCertificates0183.C5868, NewCertificates0183.C5869, NewCertificates0183.C5870, NewCertificates0183.C5871, NewCertificates0183.C5872, NewCertificates0183.C5873, NewCertificates0183.C5874, NewCertificates0183.C5875, NewCertificates0183.C5876, NewCertificates0183.C5877, NewCertificates0183.C5878, NewCertificates0183.C5879, NewCertificates0183.C5880, NewCertificates0183.C5881, NewCertificates0183.C5882, NewCertificates0183.C5883, NewCertificates0183.C5884, NewCertificates0183.C5885, NewCertificates0183.C5886, NewCertificates0183.C5887, NewCertificates0184.C5888, NewCertificates0184.C5889, NewCertificates0184.C5890, NewCertificates0184.C5891, NewCertificates0184.C5892, NewCertificates0184.C5893, NewCertificates0184.C5894, NewCertificates0184.C5895, NewCertificates0184.C5896, NewCertificates0184.C5897, NewCertificates0184.C5898, NewCertificates0184.C5899, NewCertificates0184.C5900, NewCertificates0184.C5901, NewCertificates0184.C5902, NewCertificates0184.C5903, NewCertificates0184.C5904, NewCertificates0184.C5905, NewCertificates0184.C5906, NewCertificates0184.C5907, NewCertificates0184.C5908, NewCertificates0184.C5909, NewCertificates0184.C5910, NewCertificates0184.C5911, NewCertificates0184.C5912, NewCertificates0184.C5913, NewCertificates0184.C5914, NewCertificates0184.C5915, NewCertificates0184.C5916, NewCertificates0184.C5917, NewCertificates0184.C5918, NewCertificates0184.C5919, NewCertificates0185.C5920, NewCertificates0185.C5921, NewCertificates0185.C5922, NewCertificates0185.C5923, NewCertificates0185.C5924, NewCertificates0185.C5925, NewCertificates0185.C5926, NewCertificates0185.C5927, NewCertificates0185.C5928, NewCertificates0185.C5929, NewCertificates0185.C5930, NewCertificates0185.C5931, NewCertificates0185.C5932, NewCertificates0185.C5933, NewCertificates0185.C5934, NewCertificates0185.C5935, NewCertificates0185.C5936, NewCertificates0185.C5937, NewCertificates0185.C5938, NewCertificates0185.C5939, NewCertificates0185.C5940, NewCertificates0185.C5941, NewCertificates0185.C5942, NewCertificates0185.C5943, NewCertificates0185.C5944, NewCertificates0185.C5945, NewCertificates0185.C5946, NewCertificates0185.C5947, NewCertificates0185.C5948, NewCertificates0185.C5949, NewCertificates0185.C5950, NewCertificates0185.C5951, NewCertificates0186.C5952, NewCertificates0186.C5953, NewCertificates0186.C5954, NewCertificates0186.C5955, NewCertificates0186.C5956, NewCertificates0186.C5957, NewCertificates0186.C5958, NewCertificates0186.C5959, NewCertificates0186.C5960, NewCertificates0186.C5961, NewCertificates0186.C5962, NewCertificates0186.C5963, NewCertificates0186.C5964, NewCertificates0186.C5965, NewCertificates0186.C5966, NewCertificates0186.C5967, NewCertificates0186.C5968, NewCertificates0186.C5969, NewCertificates0186.C5970, NewCertificates0186.C5971}
def U0 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U1 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U2 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U3 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U4 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U5 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U6 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U7 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U8 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U9 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U10 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U11 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U12 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U13 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U14 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U15 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U16 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U17 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U18 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U19 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U20 : QuotientMatrix := !![1, 0, 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U21 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U22 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U23 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U24 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U25 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U26 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U27 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U28 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 1, 0, 0, 0, 1, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U29 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U30 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U31 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U32 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U33 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 1, 2; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 1, 0, 2, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 1, 0, 2, 0, 0, 0, 0, 0; 2, 1, 0, 0, 0, 0, 0, 0]
def U34 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U35 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U36 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U37 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U38 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U39 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U40 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 1, 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U41 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 2, 0, 1; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 2, 0, 1, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 1, 0, 0, 0, 0, 0, 1]
def U42 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U43 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 1, 1, 1, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U44 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 1, 0, 1, 0, 1, 0; 0, 0, 0, 0, 2, 1, 0, 0; 0, 0, 1, 2, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U45 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 1, 1, 1, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 1, 0, 1, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def U46 : QuotientMatrix := !![0, 0, 0, 0, 0, 0, 2, 1; 0, 0, 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 2, 0, 1, 0; 0, 0, 0, 0, 1, 2, 0, 0; 0, 0, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 0, 0, 0; 2, 0, 1, 0, 0, 0, 0, 0; 1, 2, 0, 0, 0, 0, 0, 0]
def D0 : Finset (Fin 8 × Fin 8) := ∅
def D1 : Finset (Fin 8 × Fin 8) := {(3,5)}
def D2 : Finset (Fin 8 × Fin 8) := {(3,4)}
def D3 : Finset (Fin 8 × Fin 8) := {(1,5)}
def D4 : Finset (Fin 8 × Fin 8) := {(1,5), (3,4)}
def D5 : Finset (Fin 8 × Fin 8) := {(2,4)}
def D6 : Finset (Fin 8 × Fin 8) := {(2,4), (3,5)}
def D7 : Finset (Fin 8 × Fin 8) := {(1,5), (2,4)}
def D8 : Finset (Fin 8 × Fin 8) := {(1,7)}
def D9 : Finset (Fin 8 × Fin 8) := {(1,7), (3,5)}
def D10 : Finset (Fin 8 × Fin 8) := {(1,7), (3,4)}
def D11 : Finset (Fin 8 × Fin 8) := {(1,7), (2,4)}
def D12 : Finset (Fin 8 × Fin 8) := {(1,7), (2,4), (3,5)}
def D13 : Finset (Fin 8 × Fin 8) := {(2,6)}
def D14 : Finset (Fin 8 × Fin 8) := {(2,6), (3,5)}
def D15 : Finset (Fin 8 × Fin 8) := {(2,6), (3,4)}
def D16 : Finset (Fin 8 × Fin 8) := {(1,5), (2,6)}
def D17 : Finset (Fin 8 × Fin 8) := {(1,5), (2,6), (3,4)}
def D18 : Finset (Fin 8 × Fin 8) := {(1,7), (2,6)}
def D19 : Finset (Fin 8 × Fin 8) := {(1,7), (2,6), (3,5)}
def D20 : Finset (Fin 8 × Fin 8) := {(1,7), (2,6), (3,4)}
def D21 : Finset (Fin 8 × Fin 8) := {(0,7)}
def D22 : Finset (Fin 8 × Fin 8) := {(0,7), (3,5)}
def D23 : Finset (Fin 8 × Fin 8) := {(0,7), (3,4)}
def D24 : Finset (Fin 8 × Fin 8) := {(0,7), (1,5)}
def D25 : Finset (Fin 8 × Fin 8) := {(0,7), (1,5), (3,4)}
def D26 : Finset (Fin 8 × Fin 8) := {(0,7), (2,4)}
def D27 : Finset (Fin 8 × Fin 8) := {(0,7), (2,4), (3,5)}
def D28 : Finset (Fin 8 × Fin 8) := {(0,7), (1,5), (2,4)}
def D29 : Finset (Fin 8 × Fin 8) := {(0,7), (2,6)}
def D30 : Finset (Fin 8 × Fin 8) := {(0,7), (2,6), (3,5)}
def D31 : Finset (Fin 8 × Fin 8) := {(0,7), (2,6), (3,4)}
def D32 : Finset (Fin 8 × Fin 8) := {(0,7), (1,5), (2,6)}
def D33 : Finset (Fin 8 × Fin 8) := {(0,7), (1,5), (2,6), (3,4)}
def D34 : Finset (Fin 8 × Fin 8) := {(0,6)}
def D35 : Finset (Fin 8 × Fin 8) := {(0,6), (3,5)}
def D36 : Finset (Fin 8 × Fin 8) := {(0,6), (3,4)}
def D37 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5)}
def D38 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5), (3,4)}
def D39 : Finset (Fin 8 × Fin 8) := {(0,6), (2,4)}
def D40 : Finset (Fin 8 × Fin 8) := {(0,6), (2,4), (3,5)}
def D41 : Finset (Fin 8 × Fin 8) := {(0,6), (1,5), (2,4)}
def D42 : Finset (Fin 8 × Fin 8) := {(0,6), (1,7)}
def D43 : Finset (Fin 8 × Fin 8) := {(0,6), (1,7), (3,5)}
def D44 : Finset (Fin 8 × Fin 8) := {(0,6), (1,7), (3,4)}
def D45 : Finset (Fin 8 × Fin 8) := {(0,6), (1,7), (2,4)}
def D46 : Finset (Fin 8 × Fin 8) := {(0,6), (1,7), (2,4), (3,5)}
theorem doubled_enumeration : ((supportEdges 217591204463812800).powerset.filter fun D => ∀ i : Fin 8, 1 ≤ offSum 217591204463812800 D i ∧ offSum 217591204463812800 D i ≤ 3) = {D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16, D17, D18, D19, D20, D21, D22, D23, D24, D25, D26, D27, D28, D29, D30, D31, D32, D33, D34, D35, D36, D37, D38, D39, D40, D41, D42, D43, D44, D45, D46} := by
  decide +kernel
theorem augmentation0 : augmentation 217591204463812800 D0 = U0 := by
  decide +kernel
theorem augmentation1 : augmentation 217591204463812800 D1 = U1 := by
  decide +kernel
theorem augmentation2 : augmentation 217591204463812800 D2 = U2 := by
  decide +kernel
theorem augmentation3 : augmentation 217591204463812800 D3 = U3 := by
  decide +kernel
theorem augmentation4 : augmentation 217591204463812800 D4 = U4 := by
  decide +kernel
theorem augmentation5 : augmentation 217591204463812800 D5 = U5 := by
  decide +kernel
theorem augmentation6 : augmentation 217591204463812800 D6 = U6 := by
  decide +kernel
theorem augmentation7 : augmentation 217591204463812800 D7 = U7 := by
  decide +kernel
theorem augmentation8 : augmentation 217591204463812800 D8 = U8 := by
  decide +kernel
theorem augmentation9 : augmentation 217591204463812800 D9 = U9 := by
  decide +kernel
theorem augmentation10 : augmentation 217591204463812800 D10 = U10 := by
  decide +kernel
theorem augmentation11 : augmentation 217591204463812800 D11 = U11 := by
  decide +kernel
theorem augmentation12 : augmentation 217591204463812800 D12 = U12 := by
  decide +kernel
theorem augmentation13 : augmentation 217591204463812800 D13 = U13 := by
  decide +kernel
theorem augmentation14 : augmentation 217591204463812800 D14 = U14 := by
  decide +kernel
theorem augmentation15 : augmentation 217591204463812800 D15 = U15 := by
  decide +kernel
theorem augmentation16 : augmentation 217591204463812800 D16 = U16 := by
  decide +kernel
theorem augmentation17 : augmentation 217591204463812800 D17 = U17 := by
  decide +kernel
theorem augmentation18 : augmentation 217591204463812800 D18 = U18 := by
  decide +kernel
theorem augmentation19 : augmentation 217591204463812800 D19 = U19 := by
  decide +kernel
theorem augmentation20 : augmentation 217591204463812800 D20 = U20 := by
  decide +kernel
theorem augmentation21 : augmentation 217591204463812800 D21 = U21 := by
  decide +kernel
theorem augmentation22 : augmentation 217591204463812800 D22 = U22 := by
  decide +kernel
theorem augmentation23 : augmentation 217591204463812800 D23 = U23 := by
  decide +kernel
theorem augmentation24 : augmentation 217591204463812800 D24 = U24 := by
  decide +kernel
theorem augmentation25 : augmentation 217591204463812800 D25 = U25 := by
  decide +kernel
theorem augmentation26 : augmentation 217591204463812800 D26 = U26 := by
  decide +kernel
theorem augmentation27 : augmentation 217591204463812800 D27 = U27 := by
  decide +kernel
theorem augmentation28 : augmentation 217591204463812800 D28 = U28 := by
  decide +kernel
theorem augmentation29 : augmentation 217591204463812800 D29 = U29 := by
  decide +kernel
theorem augmentation30 : augmentation 217591204463812800 D30 = U30 := by
  decide +kernel
theorem augmentation31 : augmentation 217591204463812800 D31 = U31 := by
  decide +kernel
theorem augmentation32 : augmentation 217591204463812800 D32 = U32 := by
  decide +kernel
theorem augmentation33 : augmentation 217591204463812800 D33 = U33 := by
  decide +kernel
theorem augmentation34 : augmentation 217591204463812800 D34 = U34 := by
  decide +kernel
theorem augmentation35 : augmentation 217591204463812800 D35 = U35 := by
  decide +kernel
theorem augmentation36 : augmentation 217591204463812800 D36 = U36 := by
  decide +kernel
theorem augmentation37 : augmentation 217591204463812800 D37 = U37 := by
  decide +kernel
theorem augmentation38 : augmentation 217591204463812800 D38 = U38 := by
  decide +kernel
theorem augmentation39 : augmentation 217591204463812800 D39 = U39 := by
  decide +kernel
theorem augmentation40 : augmentation 217591204463812800 D40 = U40 := by
  decide +kernel
theorem augmentation41 : augmentation 217591204463812800 D41 = U41 := by
  decide +kernel
theorem augmentation42 : augmentation 217591204463812800 D42 = U42 := by
  decide +kernel
theorem augmentation43 : augmentation 217591204463812800 D43 = U43 := by
  decide +kernel
theorem augmentation44 : augmentation 217591204463812800 D44 = U44 := by
  decide +kernel
theorem augmentation45 : augmentation 217591204463812800 D45 = U45 := by
  decide +kernel
theorem augmentation46 : augmentation 217591204463812800 D46 = U46 := by
  decide +kernel
theorem unsigned_enumeration : unsignedPatterns 217591204463812800 = {U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, U11, U12, U13, U14, U15, U16, U17, U18, U19, U20, U21, U22, U23, U24, U25, U26, U27, U28, U29, U30, U31, U32, U33, U34, U35, U36, U37, U38, U39, U40, U41, U42, U43, U44, U45, U46} := by
  simp only [unsignedPatterns, doubled_enumeration, Finset.image_insert, Finset.image_singleton, augmentation0, augmentation1, augmentation2, augmentation3, augmentation4, augmentation5, augmentation6, augmentation7, augmentation8, augmentation9, augmentation10, augmentation11, augmentation12, augmentation13, augmentation14, augmentation15, augmentation16, augmentation17, augmentation18, augmentation19, augmentation20, augmentation21, augmentation22, augmentation23, augmentation24, augmentation25, augmentation26, augmentation27, augmentation28, augmentation29, augmentation30, augmentation31, augmentation32, augmentation33, augmentation34, augmentation35, augmentation36, augmentation37, augmentation38, augmentation39, augmentation40, augmentation41, augmentation42, augmentation43, augmentation44, augmentation45, augmentation46]
theorem tree : ∀ i : Fin 8, i ≠ 0 → (p i).val < i.val ∧ graphBit 8 217591204463812800 (e (p i)).val (e i).val = true := by
  decide +kernel
end Nut8.FiniteSupport122
