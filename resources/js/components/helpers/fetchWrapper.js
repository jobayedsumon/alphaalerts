import axios from "axios";

const fetchWrapper = axios.create({
    headers: {
        'Content-Type': 'application/json',
        'Accept': 'application/json',
    },
});

export default fetchWrapper;
