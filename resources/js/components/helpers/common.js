import Swal from "sweetalert2";

export const swalSuccess = (text) => {
    Swal.fire({
        title: "Success",
        text: text,
        icon: 'success',
        confirmButtonText: 'Ok'
    });
}

export const swalError = (text) => {
    Swal.fire({
        title: "Error",
        text: text,
        icon: 'error',
        confirmButtonText: 'Ok'
    });
}
